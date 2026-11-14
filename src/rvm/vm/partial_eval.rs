// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Partial evaluation: concrete evaluation that keeps a shadow of which
//! registers depend on unknown paths.
//!
//! The shadow covers the registers of one frame: the bodies of the queried
//! rule, or the entry code when the query is not a single rule reference.
//! Only indexing and `Move` understand tainted registers. Any other read of
//! a tainted register, or a read of an unknown root outside the frame, makes
//! the result `Unsupported`, so constructs not handled here fail closed.

use super::dispatch::InstructionOutcome;
use super::errors::Result;
use super::execution_model::ExecutionMode;
use super::machine::RegoVM;
use crate::explain::{
    ExplainError, PartialEvalResult, PartialEvalSettings, PathSegment, ResidualStatus, RuleKind,
    SourceLocation, UnknownRoot,
};
use crate::rvm::instructions::{Instruction, LiteralOrRegister};
use crate::rvm::program::Program;
use crate::value::Value;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use core::sync::atomic::{AtomicUsize, Ordering};

type Path = (UnknownRoot, Vec<PathSegment>);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Class {
    Clean,
    Prefix,
    Unknown,
}

#[derive(Debug, Clone)]
enum Taint {
    /// A strict prefix of an unknown path: the register holds the supplied
    /// part, which is incomplete.
    Prefix(Path),
    /// At or under an unknown path. `used` is set when a site consumes it.
    Unknown { path: Path, used: bool },
}

#[derive(Debug, Clone, Copy)]
enum Reason {
    OutsideFrame,
    Unconstrained,
    RuleValue,
}

/// Partial evaluation state for one evaluation.
#[derive(Debug)]
pub(super) struct PeState {
    unknowns: Vec<Path>,
    /// Register stack depth of the shadowed frame.
    frame_depth: usize,
    shadow: BTreeMap<u8, Taint>,
    unsupported: Option<(Reason, usize)>,
    /// `pc + 1` of the first other read of a tainted register, or 0.
    read_pc: AtomicUsize,
}

impl PeState {
    const fn in_frame(&self, depth: usize) -> bool {
        depth == self.frame_depth
    }

    pub(super) fn note_read(&self, reg: u8, pc: usize, depth: usize) {
        if self.in_frame(depth) && self.shadow.contains_key(&reg) {
            let _ = self.read_pc.compare_exchange(
                0,
                pc.saturating_add(1),
                Ordering::Relaxed,
                Ordering::Relaxed,
            );
        }
    }

    pub(super) fn note_write(&mut self, reg: u8, pc: usize, depth: usize) {
        if self.in_frame(depth) {
            if let Some(taint) = self.shadow.remove(&reg) {
                if is_unused(&taint) {
                    self.flag(Reason::Unconstrained, pc);
                }
            }
        }
    }

    fn flag(&mut self, reason: Reason, pc: usize) {
        self.unsupported.get_or_insert((reason, pc));
    }

    fn classify(&self, root: UnknownRoot, segments: &[PathSegment]) -> Class {
        let mut class = Class::Clean;
        for &(unknown_root, ref unknown) in &self.unknowns {
            if unknown_root != root {
                continue;
            }
            if segments.starts_with(unknown) {
                return Class::Unknown;
            }
            if unknown.starts_with(segments) {
                class = Class::Prefix;
            }
        }
        class
    }

    fn mark_used(&mut self, reg: u8) {
        if let Some(&mut Taint::Unknown { ref mut used, .. }) = self.shadow.get_mut(&reg) {
            *used = true;
        }
    }

    fn flag_unused(&mut self, pc: usize) {
        if self.shadow.values().any(is_unused) {
            self.flag(Reason::Unconstrained, pc);
        }
    }
}

impl Taint {
    fn path(&self) -> (Class, Path) {
        match *self {
            Self::Prefix(ref path) => (Class::Prefix, path.clone()),
            Self::Unknown { ref path, .. } => (Class::Unknown, path.clone()),
        }
    }
}

const fn is_unused(taint: &Taint) -> bool {
    matches!(*taint, Taint::Unknown { used: false, .. })
}

fn segment(key: &Value) -> Option<PathSegment> {
    match *key {
        Value::String(ref s) => Some(PathSegment::Key(s.to_string())),
        Value::Number(ref n) => n.as_u64().map(PathSegment::Index),
        _ => None,
    }
}

fn index(value: &Value, segment: &PathSegment) -> Value {
    match *segment {
        PathSegment::Key(ref key) => value[&Value::from(key.as_str())].clone(),
        PathSegment::Index(i) => value[&Value::from(i)].clone(),
    }
}

/// Renders a path as Rego, such as `input["user"]["role"]` or
/// `input["xs"][0]`.
fn render_path(root: UnknownRoot, segments: &[PathSegment]) -> String {
    let mut text = String::from(match root {
        UnknownRoot::Context => "context",
        _ => "input",
    });
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
            frame_depth: usize::from(rule.is_some()),
            shadow: BTreeMap::new(),
            unsupported: None,
            read_pc: AtomicUsize::new(0),
        }));
        let run = self.execute_entry_point_by_name(entry);
        let Some(mut state) = self.pe.take() else {
            return Err(ExplainError::NotEnabled);
        };
        if state.frame_depth == 0 {
            state.flag_unused(self.pc);
        }
        let read_pc = state.read_pc.load(Ordering::Relaxed);
        let rule_info = rule.and_then(|r| program.rule_infos.get(usize::from(r)));
        let kind = rule_info.map_or(RuleKind::Complete, |info| {
            if info.function_info.is_some() {
                RuleKind::Function
            } else {
                RuleKind::from(info.rule_type.clone())
            }
        });
        let unsupported = |warning: String| PartialEvalResult {
            kind,
            status: ResidualStatus::Unsupported,
            result: Value::Undefined,
            residual_queries: Vec::new(),
            warnings: alloc::vec![warning],
        };
        if let Some((reason, pc)) = state.unsupported {
            return Ok(unsupported(warning(&program, Some(reason), pc)));
        }
        if let Some(pc) = read_pc.checked_sub(1) {
            return Ok(unsupported(warning(&program, None, pc)));
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

    const fn pe_depth(&self) -> usize {
        self.register_stack.len()
    }

    fn pe_taint(&self, reg: u8) -> Option<&Taint> {
        self.pe.as_deref().and_then(|pe| pe.shadow.get(&reg))
    }

    fn pe_raw(&self, reg: u8) -> Value {
        self.registers
            .get(usize::from(reg))
            .cloned()
            .unwrap_or(Value::Undefined)
    }

    fn pe_mut(&mut self) -> Option<&mut PeState> {
        self.pe.as_deref_mut()
    }

    fn pe_set(&mut self, dest: u8, value: Value, taint: Option<Taint>) -> Result<()> {
        self.set_register(dest, value)?;
        if let (Some(taint), Some(pe)) = (taint, self.pe.as_deref_mut()) {
            pe.shadow.insert(dest, taint);
        }
        Ok(())
    }

    /// Handles an instruction that involves the shadow. Returns `None` to
    /// run it normally, in which case any read of a tainted register makes
    /// the result unsupported.
    #[cold]
    #[inline(never)]
    pub(super) fn pe_execute(
        &mut self,
        program: &Program,
        instruction: &Instruction,
    ) -> Result<Option<InstructionOutcome>> {
        let in_frame = self
            .pe
            .as_deref()
            .is_some_and(|pe| pe.in_frame(self.pe_depth()) && !pe.shadow.is_empty());
        match *instruction {
            Instruction::LoadInput { dest } => self.pe_load_root(dest, UnknownRoot::Input),
            Instruction::LoadContext { dest } => self.pe_load_root(dest, UnknownRoot::Context),
            _ if !in_frame => Ok(None),
            Instruction::Move { dest, src } => match self.pe_taint(src).cloned() {
                Some(taint) => {
                    if let Some(pe) = self.pe_mut() {
                        pe.mark_used(src);
                    }
                    let taint = match taint {
                        Taint::Unknown { path, .. } => Taint::Unknown { path, used: false },
                        prefix @ Taint::Prefix(_) => prefix,
                    };
                    let value = self.pe_raw(src);
                    self.pe_set(dest, value, Some(taint))?;
                    Ok(Some(InstructionOutcome::Continue))
                }
                None => Ok(None),
            },
            Instruction::Index {
                dest,
                container,
                key,
            } => self.pe_index(
                program,
                dest,
                container,
                &[LiteralOrRegister::Register(key)],
            ),
            Instruction::IndexLiteral {
                dest,
                container,
                literal_idx,
            } => self.pe_index(
                program,
                dest,
                container,
                &[LiteralOrRegister::Literal(literal_idx)],
            ),
            Instruction::ChainedIndex { params_index } => {
                let Some(params) = program
                    .instruction_data
                    .get_chained_index_params(params_index)
                else {
                    return Ok(None);
                };
                self.pe_index(program, params.dest, params.root, &params.path_components)
            }
            _ => Ok(None),
        }
    }

    fn pe_load_root(&mut self, dest: u8, root: UnknownRoot) -> Result<Option<InstructionOutcome>> {
        let (pc, depth) = (self.pc, self.pe_depth());
        let Some(pe) = self.pe.as_deref_mut() else {
            return Ok(None);
        };
        let taint = match pe.classify(root, &[]) {
            Class::Clean => return Ok(None),
            Class::Prefix => Taint::Prefix((root, Vec::new())),
            Class::Unknown => Taint::Unknown {
                path: (root, Vec::new()),
                used: false,
            },
        };
        let in_frame = pe.in_frame(depth);
        if !in_frame {
            pe.flag(Reason::OutsideFrame, pc);
        }
        let value = match root {
            UnknownRoot::Context => self.context.clone(),
            _ => self.input.clone(),
        };
        self.pe_set(dest, value, in_frame.then_some(taint))?;
        Ok(Some(InstructionOutcome::Continue))
    }

    fn pe_index(
        &mut self,
        program: &Program,
        dest: u8,
        container: u8,
        keys: &[LiteralOrRegister],
    ) -> Result<Option<InstructionOutcome>> {
        let Some((mut class, (root, mut segments))) = self.pe_taint(container).map(Taint::path)
        else {
            return Ok(None);
        };
        let mut value = self.pe_raw(container);
        for component in keys {
            let key = match *component {
                LiteralOrRegister::Literal(idx) => match program.literals.get(usize::from(idx)) {
                    Some(literal) => literal.clone(),
                    None => return Ok(None),
                },
                LiteralOrRegister::Register(reg) if self.pe_taint(reg).is_none() => {
                    self.pe_raw(reg)
                }
                LiteralOrRegister::Register(_) => return Ok(None),
            };
            if class != Class::Clean {
                match segment(&key) {
                    Some(seg) => {
                        segments.push(seg);
                        class = self
                            .pe
                            .as_deref()
                            .map_or(Class::Unknown, |pe| pe.classify(root, &segments));
                    }
                    None if class == Class::Prefix => class = Class::Clean,
                    None => return Ok(None),
                }
            }
            value = value[&key].clone();
        }
        if let Some(pe) = self.pe_mut() {
            pe.mark_used(container);
        }
        let taint = match class {
            Class::Clean => None,
            Class::Prefix => Some(Taint::Prefix((root, segments))),
            Class::Unknown => Some(Taint::Unknown {
                path: (root, segments),
                used: false,
            }),
        };
        self.pe_set(dest, value, taint)?;
        Ok(Some(InstructionOutcome::Continue))
    }

    /// Starts a body of the shadowed frame.
    #[cold]
    #[inline(never)]
    pub(super) fn pe_body_start(&mut self) {
        let depth = self.pe_depth();
        if let Some(pe) = self.pe_mut().filter(|pe| pe.in_frame(depth)) {
            pe.shadow.clear();
        }
    }

    /// A body of the shadowed frame completed: its value and every unknown
    /// it read must be accounted for.
    #[cold]
    #[inline(never)]
    pub(super) fn pe_body_succeeded(&mut self, result_reg: u8) {
        let (depth, pc) = (self.pe_depth(), self.pc);
        let Some(pe) = self.pe.as_deref_mut().filter(|pe| pe.in_frame(depth)) else {
            return;
        };
        if pe.shadow.remove(&result_reg).is_some() {
            pe.flag(Reason::RuleValue, pc);
        }
        pe.flag_unused(pc);
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

fn warning(program: &Program, reason: Option<Reason>, pc: usize) -> String {
    let at = location(program, pc)
        .map(|l| format!(" at {}:{}:{}", l.file, l.line, l.column))
        .unwrap_or_default();
    let text = match reason {
        None => {
            let kind = program
                .instructions
                .get(pc)
                .map(|i| {
                    let debug = format!("{i:?}");
                    debug
                        .split([' ', '{', '('])
                        .next()
                        .unwrap_or_default()
                        .to_string()
                })
                .unwrap_or_default();
            format!("`{kind}` reads a value that depends on unknown input")
        }
        Some(Reason::OutsideFrame) => {
            String::from("unknown input is read outside the queried rule's body")
        }
        Some(Reason::Unconstrained) => {
            String::from("a value that depends on unknown input is not checked")
        }
        Some(Reason::RuleValue) => String::from("the rule value depends on unknown input"),
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
