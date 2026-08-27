// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! Implicit allOf for unbound `[*]` wildcard fields.

use alloc::format;
use alloc::string::{String, ToString as _};

use anyhow::{anyhow, Result};

use crate::languages::azure_policy::ast::{Condition, FieldKind, Lhs};
use crate::rvm::instructions::{GuardMode, LoopMode, LoopStartParams};
use crate::rvm::Instruction;

use super::core::{Compiler, CountBinding};
use super::utils::{split_count_wildcard_path, split_path_without_wildcards};

impl Compiler {
    /// Check whether a condition's LHS is a field with an unbound `[*]`
    /// wildcard (i.e., not inside a count loop that covers this path).
    /// Returns the alias's fully-qualified name alongside the resolved path,
    /// since the caller needs both: the resolved path to compile against, and
    /// the FQ name to attach to the terminal instruction for causality.
    pub(super) fn has_unbound_wildcard_field(&self, lhs: &Lhs) -> Result<Option<(String, String)>> {
        let field = match lhs {
            Lhs::Field(field_node) => field_node,
            _ => return Ok(None),
        };

        let alias = match &field.kind {
            FieldKind::Alias(alias) => alias,
            _ => return Ok(None),
        };
        let path = self.resolve_alias_path(alias, &field.span)?;

        if !path.contains("[*]") {
            return Ok(None);
        }

        if self.resolve_count_binding(&path)?.is_some() {
            return Ok(None);
        }

        Ok(Some((alias.clone(), path)))
    }

    /// Check whether a condition's LHS has an inner unbound `[*]` that lives
    /// *inside* an active count binding. Returns the alias's fully-qualified
    /// name alongside the binding and resolved remainder path, for the same
    /// reason as `has_unbound_wildcard_field`.
    pub(super) fn has_inner_unbound_wildcard_field(
        &self,
        lhs: &Lhs,
    ) -> Result<Option<(String, CountBinding, String)>> {
        let field = match lhs {
            Lhs::Field(field_node) => field_node,
            _ => return Ok(None),
        };

        let alias = match &field.kind {
            FieldKind::Alias(alias) => alias,
            _ => return Ok(None),
        };
        let path = self.resolve_alias_path(alias, &field.span)?;

        if !path.contains("[*]") {
            return Ok(None);
        }

        let binding = match self.resolve_count_binding(&path)? {
            Some(b) => b,
            None => return Ok(None),
        };

        if let Some(prefix) = &binding.field_wildcard_prefix {
            let lc_prefix = prefix.to_ascii_lowercase();
            let bound_prefix = format!("{}[*].", lc_prefix);
            if let Some(remainder) = path.to_ascii_lowercase().strip_prefix(&bound_prefix) {
                let remainder = remainder.to_string();
                if remainder.contains("[*]") {
                    return Ok(Some((alias.clone(), binding, remainder)));
                }
            }
        }

        Ok(None)
    }

    /// Compile a condition where the field LHS contains `[*]` outside a
    /// count loop.  Emits implicit *allOf* (Every loop).
    pub(super) fn compile_condition_wildcard_allof(
        &mut self,
        alias: &str,
        field_path: &str,
        condition: &Condition,
    ) -> Result<u8> {
        let span = &condition.span;
        let rhs_reg = self.compile_value_or_expr(&condition.rhs, span)?;
        self.compile_allof_loop_inner(alias, None, field_path, rhs_reg, condition)
    }

    /// Recursive helper: emit one `Every` loop per `[*]` in the path.
    pub(super) fn compile_allof_loop_inner(
        &mut self,
        alias: &str,
        base_reg: Option<u8>,
        remaining_path: &str,
        rhs_reg: u8,
        condition: &Condition,
    ) -> Result<u8> {
        let (prefix, suffix) = split_count_wildcard_path(remaining_path)?;
        let prefix = prefix.to_ascii_lowercase();
        let suffix = suffix.map(|s| s.to_ascii_lowercase());
        let span = &condition.span;

        let collection_reg = match base_reg {
            Some(base) if prefix.is_empty() => base,
            Some(base) => {
                let parts = split_path_without_wildcards(&prefix)?;
                self.emit_chained_index_segments(base, &parts, span)?
            }
            None if prefix.is_empty() => self.compile_resource_root(span)?,
            None => self.compile_resource_path_value(&prefix, span)?,
        };

        let key_reg = self.alloc_register()?;
        let current_reg = self.alloc_register()?;
        let loop_result_reg = self.alloc_register()?;

        let params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::Every,
            collection: collection_reg,
            key_reg,
            value_reg: current_reg,
            result_reg: loop_result_reg,
            body_start: 0,
            loop_end: 0,
        });

        self.emit(Instruction::LoopStart { params_index }, span);
        let loop_start_pc = self.program.instructions.len().saturating_sub(1);

        let body_start = u16::try_from(self.program.instructions.len())
            .map_err(|_| anyhow!("instruction index overflow"))?;

        match suffix {
            Some(ref s) if s.contains("[*]") => {
                let inner_result =
                    self.compile_allof_loop_inner(alias, Some(current_reg), s, rhs_reg, condition)?;
                self.emit(
                    Instruction::Guard {
                        register: inner_result,
                        mode: GuardMode::Condition,
                    },
                    span,
                );
            }
            _ => {
                let element_reg = match &suffix {
                    Some(s) => {
                        let parts = split_path_without_wildcards(s)?;
                        let reg = self.emit_chained_index_segments(current_reg, &parts, span)?;
                        // Suffix present: this ChainedIndex reads the violating field off
                        // the current loop element, so it is the value causality reports.
                        let pc = self.program.instructions.len().saturating_sub(1);
                        self.record_source_alias_for_pc(pc, alias);
                        reg
                    }
                    None => {
                        // No suffix: the loop element itself is compared (e.g. an array of
                        // scalars). Its provenance comes from LoopStart's own `with_wildcard()`,
                        // so that is the instruction to tag instead of a ChainedIndex that
                        // does not exist in this shape.
                        self.record_source_alias_for_pc(loop_start_pc, alias);
                        current_reg
                    }
                };

                let cmp_reg = self.emit_policy_operator(
                    &condition.operator.kind,
                    element_reg,
                    rhs_reg,
                    &condition.operator.span,
                )?;

                self.emit(
                    Instruction::Guard {
                        register: cmp_reg,
                        mode: GuardMode::Condition,
                    },
                    span,
                );
            }
        }

        self.emit(
            Instruction::LoopNext {
                body_start,
                loop_end: 0,
            },
            span,
        );

        let loop_end = u16::try_from(self.program.instructions.len())
            .map_err(|_| anyhow!("instruction index overflow"))?;

        self.program.update_loop_params(params_index, |params| {
            params.body_start = body_start;
            params.loop_end = loop_end;
        });

        if let Some(Instruction::LoopNext { loop_end: le, .. }) =
            self.program.instructions.last_mut()
        {
            *le = loop_end;
        }

        Ok(loop_result_reg)
    }
}
