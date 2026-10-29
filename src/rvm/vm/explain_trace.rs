// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! B3 design-benchmark prototype (throwaway): compact indexed provenance with
//! a bounded recorder, plus a lazily materialized (replay) variant.
//!
//! * Static provenance is **not** built by the compiler. A condition site is
//!   identified by its program counter, and its text, location and operator
//!   are decoded from the existing `instruction_spans`/`instructions` tables
//!   only when a report is materialized.
//! * At runtime an enabled recorder appends fixed-size [`Event`]s and clones
//!   operand `Value`s (reference-count bumps) into a value table. Both tables
//!   are capped by [`TraceBudget`]; once a cap is hit, further events are
//!   counted but not stored, and the report carries a [`TraceTruncation`].
//! * [`ExplainCapture::Lazy`] records nothing while evaluating. Asking for a
//!   report replays the entry point with the recorder enabled and fails if
//!   the replayed result differs from the original one.
//! * [`ExplainDetail`] selects how many operand values are kept:
//!   `Summary` stores values only for each condition site's first event and
//!   first failing event (per-site counts stay exact); `Detailed` stores both
//!   operands of every event and returns one [`IterationRow`] per event.
//! * Optional concrete runtime paths (`input.items[17]`): a shadow table of
//!   path ids per register in the current frame, cleared on every register
//!   write and set by `LoadInput`/`LoadData`, `Move`, the index instructions,
//!   loop iteration and function-argument passing. Path nodes are interned in
//!   a bounded arena and formatted only when a report is materialized.

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use serde::Serialize;

use crate::explain::{
    ConditionExplanation, ConditionKind, DefinitionExplanation, EmissionExplanation,
    ExplanationReport, LoopWitness, Operand, Operator, Outcome, ReportedValue, RuleExplanation,
    RuleKind, SourceLocation,
};
use crate::rvm::instructions::{GuardMode, Instruction};
use crate::value::Value;

use super::machine::RegoVM;

/// When explanation data is captured.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExplainCapture {
    /// Nothing is captured and no report is available.
    #[default]
    Off,
    /// Events are captured while evaluating.
    Eager,
    /// Nothing is captured while evaluating; a report replays the evaluation.
    Lazy,
}

/// How many operand values the recorder keeps.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExplainDetail {
    /// Values only for each site's first event and first failing event.
    #[default]
    Summary,
    /// Both operand values for every event, plus per-event rows.
    Detailed,
}

/// Per-evaluation limits of the recorder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TraceBudget {
    /// Maximum number of stored events.
    pub max_events: u32,
    /// Maximum number of stored operand values.
    pub max_values: u32,
    /// Arrays, sets and objects with more elements are elided, not stored.
    pub max_value_len: u32,
    /// Maximum number of interned concrete path nodes.
    pub max_path_nodes: u32,
}

impl Default for TraceBudget {
    fn default() -> Self {
        Self {
            max_events: 16_384,
            max_values: 16_384,
            max_value_len: 64,
            max_path_nodes: 16_384,
        }
    }
}

/// The first limit that was reached.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceLimit {
    Events,
    Values,
    Paths,
}

/// Present when a report is incomplete.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TraceTruncation {
    /// First limit that was reached, if any; `None` when only values that were
    /// too large were elided.
    pub limit: Option<TraceLimit>,
    /// Events that were observed but not stored.
    pub events_dropped: u32,
    /// Operand values that were not stored (too large, or value cap reached).
    pub values_elided: u32,
    /// Concrete path nodes that could not be stored (operands lose their
    /// concrete path, not their value).
    pub paths_elided: u32,
}

/// What a static decoder (B6) knows about a condition site.
#[derive(Debug, Clone, Serialize)]
pub struct SiteStatic {
    pub pc: u32,
    pub rule: String,
    pub definition: u16,
    pub body: u16,
    pub text: String,
    pub location: Option<SourceLocation>,
    pub kind: ConditionKind,
    pub operator: Option<Operator>,
    /// Operand references as written, e.g. `input.items[_]`.
    pub left_as_written: Option<String>,
    pub right_as_written: Option<String>,
}

/// One recorded condition event (`Detailed` only).
#[derive(Debug, Clone, Serialize)]
pub struct IterationRow {
    /// Index into [`ExplainOutput::sites`].
    pub site: u32,
    pub outcome: Outcome,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub left: Option<Operand>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub right: Option<Operand>,
}

/// A report and, when it is incomplete, why.
#[derive(Debug, Clone)]
pub struct ExplainOutput {
    pub report: ExplanationReport,
    pub truncation: Option<TraceTruncation>,
    /// Statically decoded condition sites (all modes).
    pub sites: Vec<SiteStatic>,
    /// Per-event rows, in evaluation order (`Detailed` only).
    pub rows: Vec<IterationRow>,
}

/// Prototype error type.
#[derive(Debug, Clone, PartialEq)]
pub enum ExplainProtoError {
    NotEnabled,
    ReplayDiverged,
    Vm(super::VmError),
}

const NO_VALUE: u32 = u32::MAX;
const NO_PATH: u32 = u32::MAX;
const ROOT_INPUT: u32 = 0;
const ROOT_DATA: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(super) enum EventKind {
    Condition,
    BodyEnd,
    Emission,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct Event {
    pc: u32,
    v0: u32,
    v1: u32,
    p0: u32,
    p1: u32,
    rule: u16,
    definition: u16,
    body: u16,
    kind: EventKind,
    passed: bool,
}

#[derive(Debug, Default)]
pub(super) struct Recorder {
    pub(super) enabled: bool,
    pub(super) emissions: bool,
    pub(super) capture: ExplainCapture,
    /// Concrete path tracking is active (requested and recording).
    pub(super) paths: bool,
    want_paths: bool,
    detail: ExplainDetail,
    budget: TraceBudget,
    events: Vec<Event>,
    values: Vec<Value>,
    events_dropped: u32,
    values_elided: u32,
    paths_elided: u32,
    limit: Option<TraceLimit>,
    /// Summary mode: per-pc bit 0 = first event seen, bit 1 = failing seen.
    site_flags: Vec<u8>,
    touched: Vec<u32>,
    /// Path nodes: (parent, key). Ids 0 and 1 are `input` and `data`.
    nodes: Vec<(u32, Value)>,
    /// Current frame: [path of register, path of the collection a loop
    /// iterates when the register is that loop's value register].
    reg_paths: Vec<[u32; 2]>,
    path_frames: Vec<Vec<[u32; 2]>>,
}

impl Recorder {
    pub(super) fn reset(&mut self) {
        self.events.clear();
        self.values.clear();
        self.events_dropped = 0;
        self.values_elided = 0;
        self.paths_elided = 0;
        self.limit = None;
        for &pc in &self.touched {
            if let Some(flag) = self.site_flags.get_mut(pc as usize) {
                *flag = 0;
            }
        }
        self.touched.clear();
        self.nodes.clear();
        self.reg_paths.clear();
        self.path_frames.clear();
        if self.want_paths {
            self.nodes.push((NO_PATH, Value::Undefined));
            self.nodes.push((NO_PATH, Value::Undefined));
        }
    }

    /// Summary mode: whether this event's operand values are kept.
    fn wants_values(&mut self, pc: usize, passed: bool) -> bool {
        if self.detail == ExplainDetail::Detailed {
            return true;
        }
        if pc >= self.site_flags.len() {
            self.site_flags.resize(pc + 1, 0);
        }
        let flag = self.site_flags[pc];
        let bit = if flag & 1 == 0 {
            1 | if passed { 0 } else { 2 }
        } else if !passed && flag & 2 == 0 {
            2
        } else {
            return false;
        };
        if flag == 0 {
            self.touched.push(u32::try_from(pc).unwrap_or(u32::MAX));
        }
        self.site_flags[pc] = flag | bit;
        true
    }

    #[inline]
    pub(super) fn clear_path(&mut self, reg: u8) {
        if let Some(slot) = self.reg_paths.get_mut(usize::from(reg)) {
            slot[0] = NO_PATH;
        }
    }

    fn path(&self, reg: u8) -> u32 {
        self.reg_paths
            .get(usize::from(reg))
            .map_or(NO_PATH, |slot| slot[0])
    }

    fn slot(&mut self, reg: u8) -> &mut [u32; 2] {
        let index = usize::from(reg);
        if index >= self.reg_paths.len() {
            self.reg_paths.resize(index + 1, [NO_PATH; 2]);
        }
        &mut self.reg_paths[index]
    }

    fn set_path(&mut self, reg: u8, path: u32) {
        self.slot(reg)[0] = path;
    }

    fn child(&mut self, parent: u32, key: &Value) -> u32 {
        if parent == NO_PATH {
            return NO_PATH;
        }
        // Re-reading the same element (e.g. `input.role` per iteration)
        // reuses a recent node.
        let len = self.nodes.len();
        for id in (len.saturating_sub(8)..len).rev() {
            let node = &self.nodes[id];
            if node.0 == parent && node.1 == *key {
                return u32::try_from(id).unwrap_or(NO_PATH);
            }
        }
        if len >= self.budget.max_path_nodes as usize + 2 {
            self.paths_elided = self.paths_elided.saturating_add(1);
            self.note_limit(TraceLimit::Paths);
            return NO_PATH;
        }
        if len == self.nodes.capacity() {
            let max = self.budget.max_path_nodes as usize + 2;
            self.nodes.reserve_exact(len.max(64).min(max - len));
        }
        self.nodes.push((parent, key.clone()));
        u32::try_from(len).unwrap_or(NO_PATH)
    }

    fn format_path(&self, id: u32) -> Option<String> {
        if id == NO_PATH {
            return None;
        }
        let mut chain = Vec::new();
        let mut cursor = id;
        while cursor > ROOT_DATA {
            let node = self.nodes.get(cursor as usize)?;
            chain.push(&node.1);
            cursor = node.0;
        }
        let mut out = String::from(if cursor == ROOT_INPUT {
            "input"
        } else {
            "data"
        });
        for key in chain.into_iter().rev() {
            push_segment(&mut out, key);
        }
        Some(out)
    }

    fn note_limit(&mut self, limit: TraceLimit) {
        if self.limit.is_none() {
            self.limit = Some(limit);
        }
    }

    fn value(&mut self, value: &Value) -> u32 {
        let len = match *value {
            Value::Array(ref a) => a.len(),
            Value::Set(ref s) => s.len(),
            Value::Object(ref o) => o.len(),
            _ => 0,
        };
        if u32::try_from(len).map_or(true, |len| len > self.budget.max_value_len) {
            self.values_elided = self.values_elided.saturating_add(1);
            return NO_VALUE;
        }
        let index = self.values.len();
        let max = self.budget.max_values as usize;
        if index >= max {
            self.values_elided = self.values_elided.saturating_add(1);
            self.note_limit(TraceLimit::Values);
            return NO_VALUE;
        }
        if index == self.values.capacity() {
            self.values.reserve_exact(index.max(64).min(max - index));
        }
        self.values.push(value.clone());
        u32::try_from(index).unwrap_or(NO_VALUE)
    }

    /// Returns false when the event cap is reached (the event is counted).
    fn has_room(&mut self) -> bool {
        let len = self.events.len();
        let max = self.budget.max_events as usize;
        if len >= max {
            self.events_dropped = self.events_dropped.saturating_add(1);
            self.note_limit(TraceLimit::Events);
            return false;
        }
        if len == self.events.capacity() {
            self.events.reserve_exact(len.max(64).min(max - len));
        }
        true
    }

    fn truncation(&self) -> Option<TraceTruncation> {
        (self.events_dropped > 0 || self.values_elided > 0 || self.paths_elided > 0).then_some(
            TraceTruncation {
                limit: self.limit,
                events_dropped: self.events_dropped,
                values_elided: self.values_elided,
                paths_elided: self.paths_elided,
            },
        )
    }
}

fn push_segment(out: &mut String, key: &Value) {
    match *key {
        Value::String(ref s)
            if !s.is_empty()
                && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                && !s.starts_with(|c: char| c.is_ascii_digit()) =>
        {
            out.push('.');
            out.push_str(s);
        }
        _ => {
            out.push('[');
            out.push_str(&key.to_json_str().unwrap_or_default());
            out.push(']');
        }
    }
}

impl RegoVM {
    /// Select how many operand values are kept and whether concrete runtime
    /// paths are tracked (prototype API).
    pub fn set_explain_detail(&mut self, detail: ExplainDetail, paths: bool) {
        self.explain.detail = detail;
        self.explain.want_paths = paths;
        self.explain.paths = paths && self.explain.enabled;
        self.explain.reset();
    }

    /// Select when explanations are captured (prototype API).
    pub fn set_explain_capture(&mut self, capture: ExplainCapture, emissions: bool) {
        self.explain.capture = capture;
        self.explain.enabled = capture == ExplainCapture::Eager;
        self.explain.paths = self.explain.want_paths && self.explain.enabled;
        self.explain.emissions = emissions;
        self.explain.reset();
    }

    /// Set the per-evaluation recorder budget (prototype API).
    pub fn set_trace_budget(&mut self, budget: TraceBudget) {
        self.explain.budget = budget;
        self.explain.reset();
        self.explain.events.shrink_to_fit();
        self.explain.values.shrink_to_fit();
        self.explain.nodes.shrink_to_fit();
        self.explain.reset();
    }

    #[inline]
    pub(super) fn explain_reg_path(&self, reg: u8) -> u32 {
        if self.explain.paths {
            self.explain.path(reg)
        } else {
            NO_PATH
        }
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_path_root(&mut self, dest: u8, data: bool) {
        self.explain
            .set_path(dest, if data { ROOT_DATA } else { ROOT_INPUT });
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_path_copy(&mut self, dest: u8, path: u32) {
        self.explain.set_path(dest, path);
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_path_child(&mut self, dest: u8, parent: u32, key: &Value) {
        let id = self.explain.child(parent, key);
        self.explain.set_path(dest, id);
    }

    /// `ChainedIndex`: the result path is the root path plus every component.
    /// Called before the destination is written.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_chain_path(&mut self, params_index: u16, parent: u32) -> u32 {
        let program = self.program.clone();
        let Some(params) = program
            .instruction_data
            .get_chained_index_params(params_index)
        else {
            return NO_PATH;
        };
        let mut id = parent;
        for component in &params.path_components {
            let key = match *component {
                crate::rvm::instructions::LiteralOrRegister::Literal(idx) => {
                    program.literals.get(usize::from(idx)).cloned()
                }
                crate::rvm::instructions::LiteralOrRegister::Register(reg) => {
                    self.registers.get(usize::from(reg)).cloned()
                }
            };
            let Some(key) = key else {
                id = NO_PATH;
                break;
            };
            id = self.explain.child(id, &key);
        }
        id
    }

    /// Loop or comprehension start: remember the collection's path for the
    /// loop's value register.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_loop_collection(&mut self, collection: u8, value_reg: u8) {
        let path = self.explain.path(collection);
        self.explain.slot(value_reg)[1] = path;
    }

    /// Loop iteration: the value register's path is collection + key.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_iteration(&mut self, value_reg: u8, key: &Value) {
        let collection = self.explain.slot(value_reg)[1];
        let id = self.explain.child(collection, key);
        self.explain.set_path(value_reg, id);
    }

    /// Rule or function frame entry: arguments keep the caller's paths.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_push_frame(&mut self, args: &[u8]) {
        let mut frame = Vec::with_capacity(args.len() + 1);
        frame.push([NO_PATH; 2]);
        for &arg in args {
            frame.push([self.explain.path(arg), NO_PATH]);
        }
        let caller = core::mem::replace(&mut self.explain.reg_paths, frame);
        self.explain.path_frames.push(caller);
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_pop_frame(&mut self) {
        if let Some(caller) = self.explain.path_frames.pop() {
            self.explain.reg_paths = caller;
        }
    }

    /// A new body starts: only retained registers (arguments) keep paths.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_body_start(&mut self, retained: usize) {
        self.explain.reg_paths.truncate(retained);
    }

    fn explain_scope(&self) -> (u16, u16, u16) {
        self.call_rule_stack.last().map_or((u16::MAX, 0, 0), |ctx| {
            (
                ctx.rule_index,
                u16::try_from(ctx.current_definition_index).unwrap_or(u16::MAX),
                u16::try_from(ctx.current_body_index).unwrap_or(u16::MAX),
            )
        })
    }

    fn explain_push(&mut self, kind: EventKind, passed: bool, v: (u32, u32), p: (u32, u32)) {
        let (v0, v1) = v;
        let (rule, definition, body) = self.explain_scope();
        self.explain.events.push(Event {
            pc: u32::try_from(self.pc).unwrap_or(u32::MAX),
            v0,
            v1,
            p0: p.0,
            p1: p.1,
            rule,
            definition,
            body,
            kind,
            passed,
        });
    }

    /// Record a `Guard` or `AssertEq` outcome. Operands are the compared
    /// registers when the guarded value comes from a comparison.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_condition(&mut self, left: u8, right: Option<u8>, passed: bool) {
        if !self.explain.has_room() {
            return;
        }
        let operands = match right {
            Some(right) => Some((left, right)),
            None => self.pc.checked_sub(1).and_then(|prev| {
                match self.program.instructions.get(prev).copied() {
                    Some(
                        Instruction::Eq {
                            dest,
                            left: l,
                            right: r,
                        }
                        | Instruction::Ne {
                            dest,
                            left: l,
                            right: r,
                        }
                        | Instruction::Lt {
                            dest,
                            left: l,
                            right: r,
                        }
                        | Instruction::Le {
                            dest,
                            left: l,
                            right: r,
                        }
                        | Instruction::Gt {
                            dest,
                            left: l,
                            right: r,
                        }
                        | Instruction::Ge {
                            dest,
                            left: l,
                            right: r,
                        },
                    ) if dest == left => Some((l, r)),
                    _ => None,
                }
            }),
        };
        if !self.explain.wants_values(self.pc, passed) {
            self.explain_push(
                EventKind::Condition,
                passed,
                (NO_VALUE, NO_VALUE),
                (NO_PATH, NO_PATH),
            );
            return;
        }
        let (l, r) = match operands {
            Some((l, r)) => (l, Some(r)),
            None => (left, None),
        };
        let lv = self
            .registers
            .get(usize::from(l))
            .cloned()
            .unwrap_or(Value::Undefined);
        let v0 = self.explain.value(&lv);
        let p0 = self.explain_reg_path(l);
        let (v1, p1) = match r {
            Some(r) => {
                let rv = self
                    .registers
                    .get(usize::from(r))
                    .cloned()
                    .unwrap_or(Value::Undefined);
                (self.explain.value(&rv), self.explain_reg_path(r))
            }
            None => (NO_VALUE, NO_PATH),
        };
        self.explain_push(EventKind::Condition, passed, (v0, v1), (p0, p1));
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_body_end(&mut self, passed: bool) {
        if self.explain.has_room() {
            self.explain_push(
                EventKind::BodyEnd,
                passed,
                (NO_VALUE, NO_VALUE),
                (NO_PATH, NO_PATH),
            );
        }
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_emission(&mut self, value: u8) {
        if !self.explain.has_room() {
            return;
        }
        let v = self
            .registers
            .get(usize::from(value))
            .cloned()
            .unwrap_or(Value::Undefined);
        let v0 = self.explain.value(&v);
        self.explain_push(
            EventKind::Emission,
            true,
            (v0, NO_VALUE),
            (NO_PATH, NO_PATH),
        );
    }

    /// Produce the report for the last evaluation of `entry_point`, whose
    /// result was `query_result`. Eager: materialize what was recorded. Lazy:
    /// replay the evaluation with recording on, then materialize.
    pub fn take_explanation(
        &mut self,
        entry_point: &str,
        query_result: &Value,
    ) -> core::result::Result<ExplainOutput, ExplainProtoError> {
        match self.explain.capture {
            ExplainCapture::Off => Err(ExplainProtoError::NotEnabled),
            ExplainCapture::Eager => {
                let output = self.materialize(query_result);
                self.explain.reset();
                Ok(output)
            }
            ExplainCapture::Lazy => {
                self.explain.enabled = true;
                self.explain.paths = self.explain.want_paths;
                let replayed = self.execute_entry_point_by_name(entry_point);
                self.explain.enabled = false;
                self.explain.paths = false;
                let replayed = replayed.map_err(ExplainProtoError::Vm)?;
                if replayed != *query_result {
                    self.explain.reset();
                    return Err(ExplainProtoError::ReplayDiverged);
                }
                let output = self.materialize(query_result);
                self.explain.reset();
                Ok(output)
            }
        }
    }

    /// An operand: the stored value, with its concrete path when tracked,
    /// else the reference as written.
    fn reported(&self, index: u32, path: u32, as_written: Option<&String>) -> Option<Operand> {
        self.explain
            .values
            .get(index as usize)
            .map(|value| Operand {
                value: ReportedValue::Known(value.clone()),
                path: self
                    .explain
                    .format_path(path)
                    .or_else(|| as_written.cloned()),
            })
    }

    /// Static stand-in for B6: the reference an operand register was read
    /// from, as written, found by scanning back for the register's writer.
    /// Straight-line only; registers written by calls or arithmetic decode to
    /// `None`.
    fn static_path(&self, pc: usize, reg: u8, depth: u8) -> Option<String> {
        use crate::rvm::instructions::LiteralOrRegister;
        if depth > 8 {
            return None;
        }
        let program = &self.program;
        let data = &program.instruction_data;
        for at in (pc.saturating_sub(256)..pc).rev() {
            let instruction = *program.instructions.get(at)?;
            let writes = |dest: u8| dest == reg;
            let lit = |idx: u16| program.literals.get(usize::from(idx));
            match instruction {
                Instruction::LoadInput { dest } if writes(dest) => return Some("input".into()),
                Instruction::LoadData { dest } if writes(dest) => return Some("data".into()),
                Instruction::Move { dest, src } if writes(dest) => {
                    return self.static_path(at, src, depth + 1)
                }
                Instruction::IndexLiteral {
                    dest,
                    container,
                    literal_idx,
                } if writes(dest) => {
                    let mut path = self.static_path(at, container, depth + 1)?;
                    push_segment(&mut path, lit(literal_idx)?);
                    return Some(path);
                }
                Instruction::Index {
                    dest,
                    container,
                    key,
                } if writes(dest) => {
                    let mut path = self.static_path(at, container, depth + 1)?;
                    let key = self
                        .static_path(at, key, depth + 1)
                        .unwrap_or_else(|| "_".into());
                    path.push('[');
                    path.push_str(&key);
                    path.push(']');
                    return Some(path);
                }
                Instruction::ChainedIndex { params_index } => {
                    let params = data.get_chained_index_params(params_index)?;
                    if !writes(params.dest) {
                        continue;
                    }
                    let mut path = self.static_path(at, params.root, depth + 1)?;
                    for component in &params.path_components {
                        match *component {
                            LiteralOrRegister::Literal(idx) => push_segment(&mut path, lit(idx)?),
                            LiteralOrRegister::Register(r) => {
                                let key = self
                                    .static_path(at, r, depth + 1)
                                    .unwrap_or_else(|| "_".into());
                                path.push('[');
                                path.push_str(&key);
                                path.push(']');
                            }
                        }
                    }
                    return Some(path);
                }
                Instruction::LoopStart { params_index } => {
                    let params = data.get_loop_params(params_index)?;
                    if writes(params.value_reg) {
                        let mut path = self.static_path(at, params.collection, depth + 1)?;
                        path.push_str("[_]");
                        return Some(path);
                    }
                    if writes(params.key_reg) || writes(params.result_reg) {
                        return None;
                    }
                }
                Instruction::ComprehensionBegin { params_index } => {
                    let params = data.get_comprehension_begin_params(params_index)?;
                    if writes(params.value_reg) {
                        let mut path = self.static_path(at, params.collection_reg, depth + 1)?;
                        path.push_str("[_]");
                        return Some(path);
                    }
                    if writes(params.key_reg) || writes(params.result_reg) {
                        return None;
                    }
                }
                other => {
                    if writes_register(&other, reg, program) {
                        return None;
                    }
                }
            }
        }
        None
    }

    fn site_static(&self, pc: usize, rule: &str, definition: u16, body: u16) -> SiteStatic {
        let (text, location) = self.site_text(pc);
        let (kind, operator) = self.site_shape(pc);
        let operands = match self.program.instructions.get(pc) {
            Some(&Instruction::AssertEq { left, right }) => Some((pc, left, Some(right))),
            Some(&Instruction::Guard { register, .. }) => pc
                .checked_sub(1)
                .and_then(|prev| match self.program.instructions.get(prev).copied() {
                    Some(
                        Instruction::Eq { dest, left, right }
                        | Instruction::Ne { dest, left, right }
                        | Instruction::Lt { dest, left, right }
                        | Instruction::Le { dest, left, right }
                        | Instruction::Gt { dest, left, right }
                        | Instruction::Ge { dest, left, right },
                    ) if dest == register => Some((prev, left, Some(right))),
                    _ => None,
                })
                .or(Some((pc, register, None))),
            _ => None,
        };
        let (left_as_written, right_as_written) = match operands {
            Some((at, l, r)) => (
                self.static_path(at, l, 0),
                r.and_then(|r| self.static_path(at, r, 0)),
            ),
            None => (None, None),
        };
        SiteStatic {
            pc: u32::try_from(pc).unwrap_or(u32::MAX),
            rule: rule.into(),
            definition,
            body,
            text,
            location,
            kind,
            operator,
            left_as_written,
            right_as_written,
        }
    }

    fn site_text(&self, pc: usize) -> (String, Option<SourceLocation>) {
        let Some(Some(span)) = self.program.instruction_spans.get(pc) else {
            return (String::new(), None);
        };
        let Some(source) = self.program.sources.get(span.source_index) else {
            return (String::new(), None);
        };
        let text = source
            .content
            .lines()
            .nth(span.line.saturating_sub(1))
            .and_then(|line| {
                let start = span.column.saturating_sub(1);
                let mut end = (start + span.length).min(line.len());
                // String-literal token spans exclude the closing quote.
                let text = line.get(start..end)?;
                let next = line.get(end..)?.chars().next();
                if let Some(q @ ('"' | '`')) = next {
                    if text.matches(q).count() % 2 == 1 {
                        end += 1;
                    }
                }
                line.get(start..end)
            })
            .unwrap_or_default()
            .to_string();
        let location = SourceLocation {
            file: source.name.clone(),
            line: span.line,
            column: span.column,
        };
        (text, Some(location))
    }

    fn site_shape(&self, pc: usize) -> (ConditionKind, Option<Operator>) {
        let operator = pc
            .checked_sub(1)
            .and_then(|prev| self.program.instructions.get(prev))
            .and_then(|instruction| match *instruction {
                Instruction::Eq { .. } => Some(Operator::Eq),
                Instruction::Ne { .. } => Some(Operator::Ne),
                Instruction::Lt { .. } => Some(Operator::Lt),
                Instruction::Le { .. } => Some(Operator::Le),
                Instruction::Gt { .. } => Some(Operator::Gt),
                Instruction::Ge { .. } => Some(Operator::Ge),
                _ => None,
            });
        let kind = match self.program.instructions.get(pc) {
            Some(&Instruction::Guard {
                mode: GuardMode::Not,
                ..
            }) => ConditionKind::Negation,
            Some(&Instruction::Guard {
                mode: GuardMode::NotUndefined,
                ..
            }) => ConditionKind::Existence,
            Some(&Instruction::AssertEq { .. }) => ConditionKind::Comparison,
            _ if operator.is_some() => ConditionKind::Comparison,
            _ => ConditionKind::Truthiness,
        };
        (kind, operator)
    }

    /// Aggregates events per (rule, definition, body) and per condition site,
    /// so report size is bounded by program size plus stored emissions. The
    /// reported sample is the site's first failing event if any, else its
    /// first event. `Detailed` also returns one row per stored event.
    fn materialize(&self, query_result: &Value) -> ExplainOutput {
        type Sample = (u32, u32, u32, u32);
        struct Site {
            pc: u32,
            iterations: u32,
            successes: u32,
            first: Sample,
            first_failing: Option<Sample>,
        }
        #[derive(Default)]
        struct Body {
            outcome: Option<bool>,
            sites: Vec<Site>,
        }
        #[derive(Default)]
        struct Rule {
            bodies: BTreeMap<(u16, u16), Body>,
            emissions: Vec<(u16, u32)>,
        }
        let detailed = self.explain.detail == ExplainDetail::Detailed;
        let mut order: Vec<u16> = Vec::new();
        let mut rules: BTreeMap<u16, Rule> = BTreeMap::new();
        for event in &self.explain.events {
            if event.rule == u16::MAX {
                continue;
            }
            let rule = rules.entry(event.rule).or_insert_with(|| {
                order.push(event.rule);
                Rule::default()
            });
            match event.kind {
                EventKind::Emission => rule.emissions.push((event.definition, event.v0)),
                EventKind::BodyEnd => {
                    let body = rule
                        .bodies
                        .entry((event.definition, event.body))
                        .or_default();
                    body.outcome = Some(body.outcome.unwrap_or(false) || event.passed);
                }
                EventKind::Condition => {
                    let body = rule
                        .bodies
                        .entry((event.definition, event.body))
                        .or_default();
                    let sample = (event.v0, event.v1, event.p0, event.p1);
                    let site = match body.sites.iter_mut().position(|s| s.pc == event.pc) {
                        Some(i) => &mut body.sites[i],
                        None => {
                            body.sites.push(Site {
                                pc: event.pc,
                                iterations: 0,
                                successes: 0,
                                first: sample,
                                first_failing: None,
                            });
                            let last = body.sites.len() - 1;
                            &mut body.sites[last]
                        }
                    };
                    site.iterations = site.iterations.saturating_add(1);
                    if event.passed {
                        site.successes = site.successes.saturating_add(1);
                    } else if site.first_failing.is_none() {
                        site.first_failing = Some(sample);
                    }
                }
            }
        }

        let mut sites: Vec<SiteStatic> = Vec::new();
        let mut site_index: BTreeMap<u32, u32> = BTreeMap::new();
        let mut report_rules = Vec::with_capacity(order.len());
        for index in order {
            let Some(rule) = rules.remove(&index) else {
                continue;
            };
            let Some(info) = self.program.rule_infos.get(usize::from(index)) else {
                continue;
            };
            let result = self
                .rule_cache
                .get(usize::from(index))
                .filter(|entry| entry.0)
                .map_or(Value::Undefined, |entry| entry.1.clone());
            let definitions = rule
                .bodies
                .into_iter()
                .map(|((definition, body), data)| DefinitionExplanation {
                    index: usize::from(definition),
                    body: usize::from(body),
                    outcome: match data.outcome {
                        Some(true) => Outcome::Success,
                        _ => Outcome::Failure,
                    },
                    location: None,
                    conditions: data
                        .sites
                        .iter()
                        .map(|site| {
                            let st =
                                self.site_static(site.pc as usize, &info.name, definition, body);
                            let sample = site.first_failing.unwrap_or(site.first);
                            let left =
                                self.reported(sample.0, sample.2, st.left_as_written.as_ref());
                            let witness = (site.iterations > 1).then(|| LoopWitness {
                                iterations: site.iterations,
                                successes: site.successes,
                                sample_key: None,
                                sample_value: left.clone(),
                            });
                            let explanation = ConditionExplanation {
                                text: st.text.clone(),
                                outcome: if site.successes > 0 {
                                    Outcome::Success
                                } else {
                                    Outcome::Failure
                                },
                                kind: st.kind,
                                location: st.location.clone(),
                                operator: st.operator,
                                left,
                                right: self.reported(
                                    sample.1,
                                    sample.3,
                                    st.right_as_written.as_ref(),
                                ),
                                witness,
                                binding: None,
                            };
                            site_index
                                .insert(site.pc, u32::try_from(sites.len()).unwrap_or(u32::MAX));
                            sites.push(st);
                            explanation
                        })
                        .collect(),
                })
                .collect();
            let emissions = rule
                .emissions
                .iter()
                .enumerate()
                .filter_map(|(i, &(definition, value))| {
                    self.reported(value, NO_PATH, None)
                        .map(|operand| EmissionExplanation {
                            index: i,
                            definition: usize::from(definition),
                            key: None,
                            value: operand.value,
                            conditions: Vec::new(),
                        })
                })
                .collect();
            let kind = if info.function_info.is_some() {
                RuleKind::Function
            } else {
                RuleKind::from(info.rule_type.clone())
            };
            report_rules.push(RuleExplanation {
                name: info.name.clone(),
                kind,
                result: ReportedValue::Known(result),
                emissions,
                definitions,
            });
        }
        let mut rows = Vec::new();
        if detailed {
            rows.reserve_exact(self.explain.events.len());
            for event in &self.explain.events {
                if event.kind != EventKind::Condition || event.rule == u16::MAX {
                    continue;
                }
                let Some(&site) = site_index.get(&event.pc) else {
                    continue;
                };
                rows.push(IterationRow {
                    site,
                    outcome: if event.passed {
                        Outcome::Success
                    } else {
                        Outcome::Failure
                    },
                    left: self.reported(event.v0, event.p0, None),
                    right: self.reported(event.v1, event.p1, None),
                });
            }
        }
        ExplainOutput {
            report: ExplanationReport {
                query_result: query_result.clone(),
                rules: report_rules,
            },
            truncation: self.explain.truncation(),
            sites,
            rows,
        }
    }
}

/// Whether `instruction` writes register `reg` (for the static decoder).
fn writes_register(
    instruction: &Instruction,
    reg: u8,
    program: &crate::rvm::program::Program,
) -> bool {
    use Instruction::*;
    let data = &program.instruction_data;
    let dest = match *instruction {
        Load { dest, .. }
        | LoadTrue { dest }
        | LoadFalse { dest }
        | LoadNull { dest }
        | LoadBool { dest, .. }
        | LoadData { dest }
        | LoadInput { dest }
        | LoadContext { dest }
        | LoadMetadata { dest }
        | Move { dest, .. }
        | Add { dest, .. }
        | Sub { dest, .. }
        | Mul { dest, .. }
        | Div { dest, .. }
        | Mod { dest, .. }
        | Eq { dest, .. }
        | Ne { dest, .. }
        | Lt { dest, .. }
        | Le { dest, .. }
        | Gt { dest, .. }
        | Ge { dest, .. }
        | And { dest, .. }
        | Or { dest, .. }
        | Not { dest, .. }
        | HostAwait { dest, .. }
        | Index { dest, .. }
        | IndexLiteral { dest, .. }
        | ArrayNew { dest }
        | SetNew { dest }
        | Contains { dest, .. }
        | Count { dest, .. }
        | CallRule { dest, .. }
        | PolicyCondition { dest, .. } => Some(dest),
        BuiltinCall { params_index } => data.get_builtin_call_params(params_index).map(|p| p.dest),
        FunctionCall { params_index } => {
            data.get_function_call_params(params_index).map(|p| p.dest)
        }
        ObjectCreate { params_index } => {
            data.get_object_create_params(params_index).map(|p| p.dest)
        }
        ArrayCreate { params_index } => data.get_array_create_params(params_index).map(|p| p.dest),
        SetCreate { params_index } => data.get_set_create_params(params_index).map(|p| p.dest),
        VirtualDataDocumentLookup { params_index } => data
            .get_virtual_data_document_lookup_params(params_index)
            .map(|p| p.dest),
        ChainedIndex { params_index } => {
            data.get_chained_index_params(params_index).map(|p| p.dest)
        }
        _ => None,
    };
    dest == Some(reg)
}
