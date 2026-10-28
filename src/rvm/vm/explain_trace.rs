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

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

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

/// Per-evaluation limits of the recorder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TraceBudget {
    /// Maximum number of stored events.
    pub max_events: u32,
    /// Maximum number of stored operand values.
    pub max_values: u32,
    /// Arrays, sets and objects with more elements are elided, not stored.
    pub max_value_len: u32,
}

impl Default for TraceBudget {
    fn default() -> Self {
        Self {
            max_events: 16_384,
            max_values: 16_384,
            max_value_len: 64,
        }
    }
}

/// The first limit that was reached.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceLimit {
    Events,
    Values,
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
}

/// A report and, when it is incomplete, why.
#[derive(Debug, Clone)]
pub struct ExplainOutput {
    pub report: ExplanationReport,
    pub truncation: Option<TraceTruncation>,
}

/// Prototype error type.
#[derive(Debug, Clone, PartialEq)]
pub enum ExplainProtoError {
    NotEnabled,
    ReplayDiverged,
    Vm(super::VmError),
}

const NO_VALUE: u32 = u32::MAX;

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
    budget: TraceBudget,
    events: Vec<Event>,
    values: Vec<Value>,
    events_dropped: u32,
    values_elided: u32,
    limit: Option<TraceLimit>,
}

impl Recorder {
    pub(super) fn reset(&mut self) {
        self.events.clear();
        self.values.clear();
        self.events_dropped = 0;
        self.values_elided = 0;
        self.limit = None;
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
        (self.events_dropped > 0 || self.values_elided > 0).then_some(TraceTruncation {
            limit: self.limit,
            events_dropped: self.events_dropped,
            values_elided: self.values_elided,
        })
    }
}

impl RegoVM {
    /// Select when explanations are captured (prototype API).
    pub fn set_explain_capture(&mut self, capture: ExplainCapture, emissions: bool) {
        self.explain.capture = capture;
        self.explain.enabled = capture == ExplainCapture::Eager;
        self.explain.emissions = emissions;
    }

    /// Set the per-evaluation recorder budget (prototype API).
    pub fn set_trace_budget(&mut self, budget: TraceBudget) {
        self.explain.budget = budget;
        self.explain.reset();
        self.explain.events.shrink_to_fit();
        self.explain.values.shrink_to_fit();
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

    fn explain_push(&mut self, kind: EventKind, passed: bool, v0: u32, v1: u32) {
        let (rule, definition, body) = self.explain_scope();
        self.explain.events.push(Event {
            pc: u32::try_from(self.pc).unwrap_or(u32::MAX),
            v0,
            v1,
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
                        Instruction::Eq { dest, left: l, right: r }
                        | Instruction::Ne { dest, left: l, right: r }
                        | Instruction::Lt { dest, left: l, right: r }
                        | Instruction::Le { dest, left: l, right: r }
                        | Instruction::Gt { dest, left: l, right: r }
                        | Instruction::Ge { dest, left: l, right: r },
                    ) if dest == left => Some((l, r)),
                    _ => None,
                }
            }),
        };
        let (v0, v1) = match operands {
            Some((l, r)) => {
                let l = self.registers.get(usize::from(l)).cloned().unwrap_or(Value::Undefined);
                let r = self.registers.get(usize::from(r)).cloned().unwrap_or(Value::Undefined);
                (self.explain.value(&l), self.explain.value(&r))
            }
            None => {
                let v = self.registers.get(usize::from(left)).cloned().unwrap_or(Value::Undefined);
                (self.explain.value(&v), NO_VALUE)
            }
        };
        self.explain_push(EventKind::Condition, passed, v0, v1);
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_body_end(&mut self, passed: bool) {
        if self.explain.has_room() {
            self.explain_push(EventKind::BodyEnd, passed, NO_VALUE, NO_VALUE);
        }
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_emission(&mut self, value: u8) {
        if !self.explain.has_room() {
            return;
        }
        let v = self.registers.get(usize::from(value)).cloned().unwrap_or(Value::Undefined);
        let v0 = self.explain.value(&v);
        self.explain_push(EventKind::Emission, true, v0, NO_VALUE);
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
                let replayed = self.execute_entry_point_by_name(entry_point);
                self.explain.enabled = false;
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

    fn reported(&self, index: u32) -> Option<Operand> {
        self.explain
            .values
            .get(index as usize)
            .map(|value| Operand {
                value: ReportedValue::Known(value.clone()),
                path: None,
            })
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
    /// so report size is bounded by program size plus stored emissions.
    fn materialize(&self, query_result: &Value) -> ExplainOutput {
        struct Site {
            pc: u32,
            iterations: u32,
            successes: u32,
            last_passed: bool,
            sample: (u32, u32),
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
                    let body = rule.bodies.entry((event.definition, event.body)).or_default();
                    body.outcome = Some(body.outcome.unwrap_or(false) || event.passed);
                }
                EventKind::Condition => {
                    let body = rule.bodies.entry((event.definition, event.body)).or_default();
                    let site = match body.sites.iter_mut().position(|s| s.pc == event.pc) {
                        Some(i) => &mut body.sites[i],
                        None => {
                            body.sites.push(Site {
                                pc: event.pc,
                                iterations: 0,
                                successes: 0,
                                last_passed: false,
                                sample: (event.v0, event.v1),
                            });
                            let last = body.sites.len() - 1;
                            &mut body.sites[last]
                        }
                    };
                    site.iterations = site.iterations.saturating_add(1);
                    if event.passed {
                        site.successes = site.successes.saturating_add(1);
                    }
                    if event.passed != site.last_passed || site.iterations == 1 {
                        site.sample = (event.v0, event.v1);
                    }
                    site.last_passed = event.passed;
                }
            }
        }

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
                            let pc = site.pc as usize;
                            let (text, location) = self.site_text(pc);
                            let (kind, operator) = self.site_shape(pc);
                            let witness = (site.iterations > 1).then(|| LoopWitness {
                                iterations: site.iterations,
                                successes: site.successes,
                                sample_key: None,
                                sample_value: self.reported(site.sample.0),
                            });
                            ConditionExplanation {
                                text,
                                outcome: if site.successes > 0 {
                                    Outcome::Success
                                } else {
                                    Outcome::Failure
                                },
                                kind,
                                location,
                                operator,
                                left: self.reported(site.sample.0),
                                right: self.reported(site.sample.1),
                                witness,
                                binding: None,
                            }
                        })
                        .collect(),
                })
                .collect();
            let emissions = rule
                .emissions
                .iter()
                .enumerate()
                .filter_map(|(i, &(definition, value))| {
                    self.reported(value).map(|operand| EmissionExplanation {
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
        ExplainOutput {
            report: ExplanationReport {
                query_result: query_result.clone(),
                rules: report_rules,
            },
            truncation: self.explain.truncation(),
        }
    }
}
