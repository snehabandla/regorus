// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Partial evaluation: concrete evaluation with some input or context paths
//! declared unknown.
//!
//! Any read of a root that has unknown paths at or under it makes the
//! result `Unsupported`, so constructs not handled here fail closed. When
//! no such root is read, the result is `Exact` with the concrete value.

use super::dispatch::InstructionOutcome;
use super::errors::Result;
use super::execution_model::ExecutionMode;
use super::machine::RegoVM;
use crate::explain::{
    ExplainError, PartialEvalResult, PartialEvalSettings, PathSegment, ResidualStatus, RuleKind,
    SourceLocation, UnknownRoot,
};
use crate::rvm::instructions::Instruction;
use crate::rvm::program::Program;
use crate::value::Value;
use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

type Path = (UnknownRoot, Vec<PathSegment>);

#[derive(Debug, Clone, Copy)]
enum Reason {
    RootRead(UnknownRoot),
}

/// Partial evaluation state for one evaluation.
#[derive(Debug)]
pub(super) struct PeState {
    unknowns: Vec<Path>,
    unsupported: Option<(Reason, usize)>,
}

impl PeState {
    fn flag(&mut self, reason: Reason, pc: usize) {
        self.unsupported.get_or_insert((reason, pc));
    }
}

fn index(value: &Value, segment: &PathSegment) -> Value {
    match *segment {
        PathSegment::Key(ref key) => value[&Value::from(key.as_str())].clone(),
        PathSegment::Index(i) => value[&Value::from(i)].clone(),
    }
}

const fn root_name(root: UnknownRoot) -> &'static str {
    match root {
        UnknownRoot::Context => "context",
        _ => "input",
    }
}

/// Renders a path as Rego, such as `input["user"]["role"]` or
/// `input["xs"][0]`.
fn render_path(root: UnknownRoot, segments: &[PathSegment]) -> String {
    let mut text = String::from(root_name(root));
    for segment in segments {
        match *segment {
            PathSegment::Key(ref key) => {
                let quoted = Value::from(key.as_str())
                    .to_json_str_compact()
                    .unwrap_or_default();
                text.push_str(&format!("[{quoted}]"));
            }
            PathSegment::Index(i) => text.push_str(&format!("[{i}]")),
        }
    }
    text
}

impl RegoVM {
    /// Sets the unknown paths for [`partial_eval`](Self::partial_eval).
    pub fn set_partial_eval_settings(&mut self, settings: PartialEvalSettings) {
        self.pe_settings = settings;
    }

    /// Evaluates the entry point with the configured unknown paths and
    /// returns what the result depends on. The VM's input and context are
    /// the known values; none may be supplied at or under an unknown path.
    pub fn partial_eval(
        &mut self,
        entry: &str,
    ) -> core::result::Result<PartialEvalResult, ExplainError> {
        if matches!(self.next_execution_mode, ExecutionMode::Suspendable) {
            return Err(ExplainError::PartialEvalSuspendable);
        }
        let unknowns = self.validate_unknowns()?;
        let program = self.program.clone();
        let rule = program.get_entry_point(entry).and_then(|pc| {
            match (
                program.instructions.get(pc),
                program.instructions.get(pc.saturating_add(1)),
            ) {
                (
                    Some(&Instruction::CallRule { rule_index, dest }),
                    Some(&Instruction::Return { value }),
                ) if dest == value => Some(rule_index),
                _ => None,
            }
        });
        self.pe = Some(Box::new(PeState {
            unknowns,
            unsupported: None,
        }));
        let run = self.execute_entry_point_by_name(entry);
        let Some(state) = self.pe.take() else {
            return Err(ExplainError::NotEnabled);
        };
        let rule_info = rule.and_then(|r| program.rule_infos.get(usize::from(r)));
        let kind = rule_info.map_or(RuleKind::Complete, |info| {
            if info.function_info.is_some() {
                RuleKind::Function
            } else {
                RuleKind::from(info.rule_type.clone())
            }
        });
        if let Some((reason, pc)) = state.unsupported {
            return Ok(PartialEvalResult {
                kind,
                status: ResidualStatus::Unsupported,
                result: Value::Undefined,
                residual_queries: Vec::new(),
                warnings: alloc::vec![warning(&program, reason, pc)],
            });
        }
        let result = run?;
        Ok(PartialEvalResult {
            kind,
            status: ResidualStatus::Exact,
            result,
            residual_queries: Vec::new(),
            warnings: Vec::new(),
        })
    }

    fn validate_unknowns(&self) -> core::result::Result<Vec<Path>, ExplainError> {
        let mut paths: Vec<Path> = Vec::new();
        for unknown in &self.pe_settings.unknowns {
            let (root, segments) = (unknown.root, &unknown.segments);
            let text = render_path(root, segments);
            if let Some(other) = paths
                .iter()
                .find(|p| p.0 == root && (p.1.starts_with(segments) || segments.starts_with(&p.1)))
            {
                return Err(ExplainError::InvalidUnknownPath {
                    path: text,
                    reason: format!("overlaps `{}`", render_path(other.0, &other.1)),
                });
            }
            let mut value = match root {
                UnknownRoot::Context => self.context.clone(),
                _ => self.input.clone(),
            };
            for segment in segments {
                value = index(&value, segment);
            }
            // The VM's input is null until it is set.
            let absent = matches!(value, Value::Undefined)
                || (segments.is_empty() && matches!(value, Value::Null));
            if !absent {
                return Err(ExplainError::UnknownValueSupplied { path: text });
            }
            paths.push((root, segments.clone()));
        }
        Ok(paths)
    }

    /// Handles an instruction that involves unknown paths. Returns `None`
    /// to run it normally.
    #[cold]
    #[inline(never)]
    pub(super) fn pe_execute(
        &mut self,
        _program: &Program,
        instruction: &Instruction,
    ) -> Result<Option<InstructionOutcome>> {
        let root = match *instruction {
            Instruction::LoadInput { .. } => UnknownRoot::Input,
            Instruction::LoadContext { .. } => UnknownRoot::Context,
            _ => return Ok(None),
        };
        let pc = self.pc;
        if let Some(pe) = self.pe.as_deref_mut() {
            if pe.unknowns.iter().any(|p| p.0 == root) {
                pe.flag(Reason::RootRead(root), pc);
            }
        }
        Ok(None)
    }
}

fn location(program: &Program, pc: usize) -> Option<SourceLocation> {
    let span = program.get_instruction_span(pc)?;
    Some(SourceLocation {
        file: program.sources.get(span.source_index)?.name.clone(),
        line: span.line,
        column: span.column,
    })
}

fn warning(program: &Program, reason: Reason, pc: usize) -> String {
    let at = location(program, pc)
        .map(|l| format!(" at {}:{}:{}", l.file, l.line, l.column))
        .unwrap_or_default();
    let text = match reason {
        Reason::RootRead(root) => format!("`{}` has unknown paths and is read", root_name(root)),
    };
    format!("partial evaluation unsupported: {text}{at}")
}

#[cfg(test)]
#[allow(
    clippy::panic_in_result_fn,
    clippy::indexing_slicing,
    clippy::field_reassign_with_default,
    clippy::shadow_unrelated
)]
mod tests;
