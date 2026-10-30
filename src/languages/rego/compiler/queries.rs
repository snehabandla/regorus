// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::as_conversions,
    clippy::pattern_type_mismatch
)]

use super::{
    Compiler, CompilerError, ComprehensionType, ContextType, HeadKey, ObjectHead, Register, Result,
};
use crate::ast::{self, LiteralStmt, Query};
use crate::lexer::Span;
use crate::rvm::instructions::{GuardMode, ObjectDeepSetParams};
use crate::rvm::program::RuleType;
use crate::rvm::Instruction;
use crate::Value;
use alloc::format;
use alloc::vec::Vec;

impl<'a> Compiler<'a> {
    pub(super) fn compile_query(&mut self, query: &Query) -> Result<()> {
        self.push_scope();

        let result = {
            let schedule = match &self.policy.inner.schedule {
                Some(s) => s
                    .queries
                    .get_checked(self.current_module_index, query.qidx)
                    .map_err(|err| {
                        CompilerError::General {
                            message: format!("schedule out of bounds: {err}"),
                        }
                        .at(&query.span)
                    })?,
                None => None,
            };

            let ordered_stmts: Vec<&LiteralStmt> = match schedule {
                Some(schedule) => schedule
                    .order
                    .iter()
                    .map(|i| &query.stmts[*i as usize])
                    .collect(),
                None => query.stmts.iter().collect(),
            };
            self.hoist_loops_and_compile_statements(&ordered_stmts)
        };

        self.pop_scope();

        result
    }

    pub(super) fn hoist_loops_and_compile_statements(
        &mut self,
        stmts: &[&LiteralStmt],
    ) -> Result<()> {
        for (idx, stmt) in stmts.iter().enumerate() {
            if !stmt.with_mods.is_empty() {
                return Err(CompilerError::WithKeywordUnsupported.at(&stmt.span));
            }
            let loop_exprs = self.get_statement_loops(stmt)?;

            if !loop_exprs.is_empty() {
                return self.compile_hoisted_loops(&stmts[idx..], &loop_exprs);
            }

            if matches!(&stmt.literal, ast::Literal::SomeIn { .. }) {
                if let ast::Literal::SomeIn {
                    ref key,
                    ref value,
                    ref collection,
                    ..
                } = &stmt.literal
                {
                    let some_result_reg = self.compile_some_in_loop_with_remaining_statements(
                        key,
                        value,
                        collection,
                        &stmts[idx..],
                    )?;
                    // Inside an `every` body a `some ... in` acts as a condition
                    // on the current iteration: if it matches nothing the
                    // iteration must fail. Unlike a top-level rule body (where
                    // per-iteration context yields produce the results), the
                    // `every` body has no yield, so the loop result register is
                    // otherwise discarded. Guard on it so a `some` that matches
                    // nothing fails the enclosing `every` iteration.
                    if matches!(
                        self.context_stack.last().map(|c| &c.context_type),
                        Some(ContextType::Every)
                    ) {
                        self.emit_instruction(
                            Instruction::Guard {
                                register: some_result_reg,
                                mode: GuardMode::Condition,
                            },
                            &stmt.span,
                        );
                    }
                    return Ok(());
                }
            }

            self.compile_single_statement(stmt)?;
        }

        self.hoist_loops_and_emit_context_yield()
    }

    pub(super) fn hoist_loops_and_emit_context_yield(&mut self) -> Result<()> {
        if let Some(context) = self.context_stack.last() {
            match &context.context_type {
                ContextType::Every => {
                    return Ok(());
                }
                ContextType::Rule(_) | ContextType::Comprehension(_) => {}
            }
        }

        let (key_expr, value_expr, object_head) = match self.context_stack.last_mut() {
            Some(context) => {
                if context.key_value_loops_hoisted {
                    return self.emit_context_yield();
                }
                (
                    context.key_expr.clone(),
                    context.value_expr.clone(),
                    context.object_head.clone(),
                )
            }
            None => return Ok(()),
        };

        let mut key_value_loops = Vec::new();

        if let Some(expr) = key_expr.as_ref() {
            key_value_loops.extend(self.get_expr_loops(expr)?);
        }

        for key in object_head.iter().flat_map(|head| head.keys.iter()) {
            if let HeadKey::Expr(expr) = key {
                key_value_loops.extend(self.get_expr_loops(expr)?);
            }
        }

        if let Some(expr) = value_expr.as_ref() {
            key_value_loops.extend(self.get_expr_loops(expr)?);
        }

        if !key_value_loops.is_empty() {
            if let Some(context) = self.context_stack.last_mut() {
                context.key_value_loops_hoisted = true;
            }
            self.compile_hoisted_loops(&[], &key_value_loops)
        } else {
            self.emit_context_yield()
        }
    }

    pub(super) fn emit_context_yield(&mut self) -> Result<()> {
        if let Some(context) = self.context_stack.last().cloned() {
            let dest_register = context.dest_register;
            let span = &context.span;
            let value_register = match context.value_expr {
                Some(expr) => self.compile_rego_expr(&expr)?,
                None if context.value_literal.is_some() => {
                    let literal = context.value_literal.clone().unwrap_or(Value::Bool(true));
                    self.load_literal_value(&literal, span)
                        .map_err(|e| CompilerError::from(e).at(span))?
                }
                None => {
                    let value_reg = self.alloc_register()?;
                    self.emit_instruction(
                        Instruction::LoadBool {
                            dest: value_reg,
                            value: true,
                        },
                        span,
                    );
                    value_reg
                }
            };

            let key_register = context
                .key_expr
                .map(|key_expr| self.compile_rego_expr(&key_expr))
                .unwrap_or(Ok(value_register))?;

            match context.context_type {
                ContextType::Comprehension(ComprehensionType::Array) => {
                    self.emit_instruction(
                        Instruction::ComprehensionYield {
                            value_reg: value_register,
                            key_reg: None,
                        },
                        span,
                    );
                }
                ContextType::Comprehension(ComprehensionType::Set) => {
                    self.emit_instruction(
                        Instruction::ComprehensionYield {
                            value_reg: value_register,
                            key_reg: None,
                        },
                        span,
                    );
                }
                ContextType::Rule(RuleType::PartialSet) => {
                    self.emit_instruction(
                        Instruction::SetAdd {
                            set: dest_register,
                            value: value_register,
                        },
                        span,
                    );
                }
                ContextType::Comprehension(ComprehensionType::Object) => {
                    self.emit_instruction(
                        Instruction::ComprehensionYield {
                            value_reg: value_register,
                            key_reg: Some(key_register),
                        },
                        span,
                    );
                }
                ContextType::Rule(RuleType::PartialObject) => match context.object_head {
                    Some(head) => {
                        self.emit_object_head_set(&head, dest_register, value_register, span)?
                    }
                    None => {
                        self.emit_instruction(
                            Instruction::ObjectSet {
                                obj: dest_register,
                                key: key_register,
                                value: value_register,
                            },
                            span,
                        );
                    }
                },
                ContextType::Rule(RuleType::Complete) => {
                    self.emit_instruction(
                        Instruction::Move {
                            dest: dest_register,
                            src: value_register,
                        },
                        span,
                    );
                }
                ContextType::Every => {}
            }
            Ok(())
        } else {
            Err(CompilerError::MissingYieldContext.into())
        }
    }

    /// Store `value_register` below the head keys of a partial object rule.
    fn emit_object_head_set(
        &mut self,
        head: &ObjectHead,
        dest_register: Register,
        value_register: Register,
        span: &Span,
    ) -> Result<()> {
        let mut key_registers = Vec::with_capacity(head.keys.len());
        for key in &head.keys {
            let register = match key {
                HeadKey::Expr(expr) => self.compile_rego_expr(expr)?,
                HeadKey::Field(field) => self
                    .load_literal_value(field, span)
                    .map_err(|e| CompilerError::from(e).at(span))?,
            };
            key_registers.push(register);
        }

        match key_registers.as_slice() {
            [key] if !head.multi_value && !head.deep => {
                self.emit_instruction(
                    Instruction::ObjectSet {
                        obj: dest_register,
                        key: *key,
                        value: value_register,
                    },
                    span,
                );
            }
            _ => {
                let params_index = self
                    .program
                    .instruction_data
                    .add_object_deep_set_params(ObjectDeepSetParams {
                        obj: dest_register,
                        keys: key_registers,
                        value: value_register,
                        multi_value: head.multi_value,
                    })
                    .ok_or_else(|| super::CompilerError::General {
                        message: alloc::string::String::from(
                            "ObjectDeepSet parameter table exhausted",
                        ),
                    })?;
                self.emit_instruction(Instruction::ObjectDeepSet { params_index }, span);
            }
        }
        Ok(())
    }

    pub(super) fn compile_single_statement(&mut self, stmt: &LiteralStmt) -> Result<()> {
        match &stmt.literal {
            ast::Literal::Expr { expr, .. } => {
                let assert_condition = !matches!(expr.as_ref(), ast::Expr::AssignExpr { .. });
                let _condition_reg =
                    self.compile_rego_expr_with_span(expr, &stmt.span, assert_condition)?;
            }
            ast::Literal::SomeIn { .. } => {
                return Err(CompilerError::SomeInNotHoisted.at(&stmt.span));
            }
            ast::Literal::Every {
                key,
                value,
                domain,
                query,
                ..
            } => {
                self.compile_every_quantifier(key, value, domain, query, &stmt.span)?;
            }
            ast::Literal::SomeVars { vars, .. } => {
                for var in vars {
                    self.add_unbound_variable(var.text());
                }
            }
            ast::Literal::NotExpr { expr, .. } => {
                let expr_reg = self.with_soft_assert_mode(true, |compiler| {
                    compiler.compile_rego_expr_with_span(expr, expr.span(), false)
                })?;

                let negated_reg = self.alloc_register()?;
                self.emit_instruction(
                    Instruction::Not {
                        dest: negated_reg,
                        operand: expr_reg,
                    },
                    &stmt.span,
                );

                self.emit_instruction(
                    Instruction::Guard {
                        register: negated_reg,
                        mode: GuardMode::Condition,
                    },
                    &stmt.span,
                );
            }
        }
        Ok(())
    }
}
