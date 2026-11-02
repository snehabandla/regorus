// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Runtime evaluation trace for causality / explanation reporting.
//!
//! This module provides a lightweight, append-only trace that captures the
//! runtime outcomes needed to produce causality reports.  All structural
//! metadata (provenance paths, condition text, operators) lives in the
//! compiled `Program` via [`crate::static_provenance`]; the trace only
//! records:
//!
//! - Which conditions passed / failed and their runtime values.
//! - Loop iteration statistics and sample witnesses.
//! - Which rule definitions were attempted and their outcomes.
//! - Assumptions recorded when unknown input handling is active.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use serde::Serialize;

use crate::value::Value;

// ---------------------------------------------------------------------------
// Settings
// ---------------------------------------------------------------------------

/// Controls how much runtime value information is captured.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ValueMode {
    /// Redact values that look like secrets (password, token, …).
    #[default]
    Redacted,
    /// Capture all values as-is.
    Full,
}

/// Controls which conditions are included in the final report.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ConditionMode {
    /// Only the primary (typically last) condition per block.
    #[default]
    PrimaryOnly,
    /// All conditions that contributed to the block's outcome.
    AllContributing,
}

/// Controls which portion of the rule report is materialized.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExplanationScope {
    /// Include explanations for every emitted result.
    #[default]
    AllEmissions,
    /// Include explanations for a single emitted result.
    SingleEmission,
    /// Suppress per-emission details and keep only the rule-level summary.
    RuleSummary,
}

/// Controls the amount of explanation detail materialized.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExplanationDetail {
    /// Reserve only the shortest useful causal set.
    Compact,
    /// Keep the current end-user default output.
    #[default]
    Standard,
    /// Include the fullest available explanation detail.
    Full,
}

/// Controls whether the engine runs in causality or partial-evaluation mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum EvaluationMode {
    /// One sufficient explanation, short-circuit after first success.
    #[default]
    Causality,
    /// Explore all branches, collect disjunctive assumption sets.
    PartialEval,
}

/// Settings governing explanation capture and reporting.
#[derive(Debug, Clone)]
pub struct ExplanationSettings {
    pub enabled: bool,
    pub value_mode: ValueMode,
    pub condition_mode: ConditionMode,
    pub scope: ExplanationScope,
    pub detail: ExplanationDetail,
    pub emission_index: Option<usize>,
    pub emission_value: Option<Value>,
    pub assume_unknown_input: bool,
    pub eval_mode: EvaluationMode,
    /// Paths treated as unknown for partial evaluation.
    /// Default: `["input"]`. A path is considered unknown if it equals
    /// or is a child of any entry (e.g. `"input"` matches `"input.foo"`).
    pub unknowns: Vec<String>,
    /// Maximum number of distinct derivations reported per repeated
    /// partial-set value. A partial-set value can be produced by several
    /// derivations (for example a constant message emitted once per
    /// non-compliant resource). With the default `1`, each emission explains
    /// only its first derivation and the report is unchanged. With a larger
    /// value, every emission also carries a `derivations` list of up to this
    /// many distinct derivations in trace order. `0` is treated as `1`.
    pub max_derivations: usize,
}

impl Default for ExplanationSettings {
    fn default() -> Self {
        Self {
            enabled: false,
            value_mode: ValueMode::default(),
            condition_mode: ConditionMode::default(),
            scope: ExplanationScope::default(),
            detail: ExplanationDetail::default(),
            emission_index: None,
            emission_value: None,
            assume_unknown_input: false,
            eval_mode: EvaluationMode::default(),
            unknowns: vec![String::from("input")],
            max_derivations: 1,
        }
    }
}

impl ExplanationSettings {
    /// Check whether `path` falls under one of the configured unknown prefixes.
    pub fn is_unknown_path(&self, path: &str) -> bool {
        for prefix in &self.unknowns {
            if path == prefix.as_str()
                || path.starts_with(&alloc::format!("{}.", prefix))
                || path.starts_with(&alloc::format!("{}[", prefix))
            {
                return true;
            }
        }
        false
    }
}

// ---------------------------------------------------------------------------
// Trace events
// ---------------------------------------------------------------------------

/// Index into `EvaluationTrace::captured_values`.
type ValueIdx = u16;

/// Outcome of a single assertion instruction.
#[derive(Debug, Clone)]
pub struct ConditionOutcome {
    /// Program counter (instruction index) of the assertion.
    pub pc: u32,
    /// Did the condition pass?
    pub passed: bool,
    /// Was this an assumption (unknown input assumed to hold)?
    pub assumed: bool,
    /// Index of the actual (LHS) value in `captured_values`, if captured.
    pub actual_value_idx: Option<ValueIdx>,
    /// Runtime provenance path for the actual value, if available.
    pub actual_path: Option<String>,
    /// A negated reference was undefined before its boolean result was computed.
    pub actual_absent: bool,
    /// Index of the expected (RHS) value in `captured_values`, if captured.
    pub expected_value_idx: Option<ValueIdx>,
    /// Runtime provenance path for the expected value, if available.
    pub expected_path: Option<String>,
    /// Index of the loop summary in `loop_stats`, if this condition has one.
    pub loop_stat_idx: Option<ValueIdx>,
    /// Rule index that was active when this outcome was recorded. Mirrors
    /// `Assumption::rule_index`; used by causality materialization to attach
    /// helper-body conditions back to the outer truthiness condition that
    /// invoked the helper.
    pub rule_index: u16,
}

/// Statistics for a completed loop.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct LoopStat {
    /// PC of the `LoopStart` instruction.
    pub pc: u32,
    /// Condition outcome index this loop summary should be attached to, when known.
    pub anchor_condition_idx: Option<u32>,
    /// Total iterations executed.
    pub total_iterations: u32,
    /// Iterations that succeeded (body completed without failure).
    pub success_count: u32,
    /// Sample successful key (index into `captured_values`).
    pub sample_key: Option<ValueIdx>,
    /// Sample successful value (index into `captured_values`).
    pub sample_value: Option<ValueIdx>,
    /// Runtime provenance of the iterated collection, when known. Witness
    /// samples are redacted by this path like operands are by theirs.
    pub collection_path: Option<crate::Rc<str>>,
    /// Number of partial-set emissions recorded when the loop finished. The
    /// value at position `i` of `emission_outcomes` was emitted after this
    /// loop finished exactly when `emissions_before_exit <= i`.
    pub emissions_before_exit: u32,
    /// Iteration id of the innermost loop of the same rule frame that was
    /// running when this loop started; `None` for a loop at body level. An
    /// emission owns this loop only if this iteration was active when it
    /// was emitted.
    pub enclosing_iteration: Option<u32>,
    /// Runtime provenance of the sample value, when known.
    pub sample_path: Option<crate::Rc<str>>,
}

/// Outcome of a rule definition evaluation.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct RuleOutcome {
    /// Rule index in `Program::rule_infos`.
    pub rule_index: u16,
    /// Which definition within the rule (0-based).
    pub definition_index: u16,
    /// Did this definition succeed?
    pub succeeded: bool,
    /// Index of the result value in `captured_values`, if captured.
    pub result_value_idx: Option<ValueIdx>,
    /// Whether this is a rule-level summary outcome (recorded once at
    /// `finalize_rule_frame_data`) rather than a per-definition outcome.
    /// Materializers use this to surface a per-rule `result` while keeping
    /// per-definition entries distinct.
    pub is_summary: bool,
    /// Runtime provenance of the result value, when it was read from data
    /// (set on summary outcomes), so a report can redact a helper's result by
    /// where it came from.
    pub result_path: Option<String>,
    /// Number of condition outcomes recorded when this outcome was recorded,
    /// so a report can find the call that finished just before a condition.
    pub conditions_recorded: u32,
    /// The call recorded an assumption at any depth (summary outcomes), so
    /// its result is not concretely known.
    pub assumption_dependent: bool,
}

/// A single emitted result value for a partial-set rule.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct EmissionOutcome {
    /// Rule index in `Program::rule_infos`.
    pub rule_index: u16,
    /// Definition that produced this emission.
    pub definition_index: u16,
    /// Start index into `condition_outcomes` for the active body window.
    pub condition_start_index: u32,
    /// End index into `condition_outcomes` for the active body window.
    pub condition_end_index: u32,
    /// Index of the emitted value in `captured_values`.
    pub value_idx: Option<ValueIdx>,
    /// Iteration ids of the loops of the emitting rule frame that were
    /// running at the emission, outermost first.
    pub active_iterations: Vec<u32>,
    /// Runtime provenance of the emitted value, when it was read from data.
    pub value_path: Option<String>,
}

/// An assumption recorded when unknown input handling skips an assertion.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Assumption {
    /// What kind of assumption was made.
    pub kind: AssumptionKind,
    /// Human-readable input path, e.g. `"input.role"`.
    pub input_path: String,
    /// Text of the condition that was assumed, e.g. `"input.role == \"admin\""`.
    pub condition_text: String,
    /// PC of the assertion that was skipped.
    pub pc: u32,
    /// The comparison operator, e.g. `"=="`, `"!="`, `"<"`.
    /// `None` for existence checks.
    pub operator: Option<String>,
    /// The operator as the policy author wrote it, when the source language
    /// names it differently from the normalized symbol in `operator` (Azure
    /// Policy's `notEquals` vs `!=`). `None` for Rego, whose authored form is
    /// the symbol.
    pub builtin_name: Option<String>,
    /// The non-input value that was compared against, e.g. `"admin"`.
    /// `None` for existence checks or when the value is not available.
    pub assumed_value: Option<Value>,
    /// Runtime provenance of `assumed_value` when it was read from data, so
    /// a report can redact it by its path like an operand.
    pub assumed_value_path: Option<String>,
    /// Rule index when the assumption was recorded (PE mode).
    pub rule_index: u16,
    /// Definition index within the rule (PE mode).
    pub definition_index: u16,
    /// Loop iteration index when the assumption was recorded (PE mode).
    /// `None` when not inside a loop or when loop tracking is not active.
    pub iteration_index: Option<u32>,
    /// Conjunction scope ID — assumptions with the same conjunction_id belong
    /// to the same rule body execution (including sub-rule calls).
    pub conjunction_id: u32,
    /// If this assumption was recorded inside a `not` body, this holds the
    /// negation scope ID.  In `materialize_pe`, inner assumptions with the
    /// same `negation_scope_id` are grouped under their parent
    /// `NegationHolds` assumption.  Causality mode ignores this field.
    pub negation_scope_id: Option<u32>,
    /// For `NegationHolds` assumptions only: the negation scope ID of the
    /// inner body this negation owns.  Used in `materialize_pe` to find
    /// which inner assumptions belong to this negation.
    pub owned_negation_scope_id: Option<u32>,
    /// When the assumption originates from indexing a known data object with
    /// an unknown input key (e.g. `data.perms[input.role]`), this captures
    /// the concrete data object so `materialize_pe` can invert the lookup.
    pub data_lookup_context: Option<DataLookupContext>,
    /// Set to `true` retroactively at definition-end (in `rules.rs`) when the
    /// enclosing definition failed to emit / assign a value. Materialize-time
    /// filter: `materialize_pe` skips orphaned assumptions so a concretely-
    /// false downstream condition prunes any assumptions recorded earlier in
    /// the body (including assumptions recorded inside helper calls). Not
    /// consulted in causality mode — causality still attaches assumptions to
    /// their recording definition for explainability.
    pub orphaned: bool,
    /// Rule frames that were on the call stack when this assumption was
    /// recorded, outermost first, excluding the rule that recorded it (which
    /// is already `rule_index`). Empty when the assumption was recorded
    /// directly in the body of the rule being evaluated.
    ///
    /// Each rule definition opens its own conjunction scope, so a residual
    /// recorded inside a helper lands in its own disjunct and cannot be
    /// attributed to the rule that owns it by grouping alone. This chain is
    /// what lets a consumer join it back to the owning rule at any call depth.
    pub call_chain: Vec<CallFrame>,
}

/// One calling rule frame captured at assumption-record time.
///
/// Carries indices rather than resolved names so the trace stays cheap; the
/// report layer resolves them against the program exactly the way it resolves
/// the recording rule's own attribution.
#[derive(Debug, Clone)]
pub struct CallFrame {
    /// Index of the calling rule.
    pub rule_index: u16,
    /// Definition index active in that rule when it made the call. Needed to
    /// resolve the body start row, which is what disambiguates two bodies of
    /// a same-named rule.
    pub definition_index: u16,
    /// PC of the call site inside this frame.
    pub call_pc: u32,
    /// Conjunction scope active in this frame when it made the call. Partial
    /// evaluation folds the callee's residual back into this conjunction, so
    /// a helper call groups with its caller instead of forming a sibling
    /// disjunct. Not serialized; it is internal linkage, not author-facing.
    pub conjunction_id: u32,
}

/// Context for inverting a data lookup during partial evaluation.
///
/// When `data.some_object[input.some_key] == value`, the data object is known
/// but the key is unknown. By storing the object we can later invert: find
/// which key(s) in the object map to the compared value.
#[derive(Debug, Clone)]
pub struct DataLookupContext {
    /// The concrete data object that was indexed.
    pub data_object: Value,
    /// The full input path of the unknown key, e.g. `"input.user.role"`.
    pub key_input_path: String,
}

/// Kinds of assumptions that can be recorded.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum AssumptionKind {
    /// An input path was assumed to exist (not undefined).
    Exists,
    /// A condition involving input was assumed to hold (evaluate to true).
    ConditionHolds,
    /// An input collection was assumed to exist for iteration.
    CollectionExists,
    /// A negation was assumed to hold (the negated rule depends on unknowns).
    NegationHolds,
}

// ---------------------------------------------------------------------------
// Warnings
// ---------------------------------------------------------------------------

/// Stable identifier for a partial-evaluation warning.
///
/// Consumers switch on this rather than matching the message text, so a
/// message can be reworded or translated without breaking them. Adding a
/// variant is not a breaking change for consumers that handle unknown codes,
/// hence `#[non_exhaustive]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum PartialEvalWarningCode {
    /// The residual could not be distributed within the disjunct limit, so it
    /// is reported in its undistributed form: a strict over-approximation that
    /// says the policy applies more often than it really does.
    DistributionOverflow,
    /// A comprehension yielded a value that depends on an assumed input, so
    /// aggregations over that result may be unsound.
    ComprehensionUnsound,
    /// An `every` ran over a collection at an unknown path and is therefore
    /// undefined rather than vacuously true.
    EveryOverUnknown,
}

/// A non-fatal caveat about a partial-evaluation result.
#[derive(Debug, Clone, serde::Serialize)]
pub struct PartialEvalWarning {
    /// What kind of caveat this is. Part of the contract; never reworded.
    pub code: PartialEvalWarningCode,
    /// Diagnostic detail, including engine-internal context such as program
    /// counters. Intended for engine debugging, not for display to a policy
    /// author - a consumer that surfaces warnings should phrase its own
    /// message from `code`.
    pub message: String,
}

// ---------------------------------------------------------------------------
// EvaluationTrace
// ---------------------------------------------------------------------------

/// Lightweight, append-only trace of runtime evaluation outcomes.
///
/// Created fresh for each evaluation.  After evaluation completes, the trace
/// is combined with the `Program`'s static metadata to produce the
/// materialized report.
#[derive(Debug, Default)]
pub struct EvaluationTrace {
    /// Condition outcomes in evaluation order.
    pub condition_outcomes: Vec<ConditionOutcome>,
    /// Captured runtime values (Rc-bumped, no deep copy).
    pub captured_values: Vec<Value>,
    /// Loop statistics.
    pub loop_stats: Vec<LoopStat>,
    /// Rule definition outcomes.
    pub rule_outcomes: Vec<RuleOutcome>,
    /// Emitted values for partial-set rules.
    pub emission_outcomes: Vec<EmissionOutcome>,
    /// Assumptions from unknown input handling.
    pub assumptions: Vec<Assumption>,
    /// Non-fatal caveats about the partial-evaluation result.
    pub warnings: Vec<PartialEvalWarning>,
    /// Monotonically increasing counter for unique iteration IDs.
    pub next_iteration_id: u32,
    /// Monotonically increasing counter for conjunction scope IDs.
    pub next_conjunction_id: u32,
    /// Monotonically increasing counter for negation scope IDs.
    pub next_negation_scope_id: u32,
    /// Stack of active negation scope IDs.  Assumptions recorded while this
    /// stack is non-empty get tagged with the top-of-stack ID.
    pub negation_scope_stack: Vec<u32>,
    /// Set to `true` during PE mode when the top-level queried rule has at
    /// least one definition that succeeded without any assumptions.  When set,
    /// `materialize_pe` returns empty residual queries because the result is
    /// fully determined by concrete evaluation.
    pub definitive_result: bool,
    /// Runtime paths of `value` entries read from `{name, value}` objects whose
    /// `name` is a sensitive name (recorded only in `ValueMode::Redacted`).
    /// A value at or under one of these paths is redacted wherever it is
    /// reported, even after it is taken out of its object.
    pub sensitive_value_paths: alloc::collections::BTreeSet<String>,
    /// `sensitive_value_paths` reached its cap; every path ending in a
    /// `value` segment is then treated as sensitive.
    pub sensitive_value_paths_overflowed: bool,
    /// String keys of objects iterated at a sensitive path (recorded only in
    /// `ValueMode::Redacted`). The keys of a secret collection are secret too,
    /// but a key has no path of its own, so it is redacted by value.
    pub sensitive_keys: alloc::collections::BTreeSet<Value>,
    /// `sensitive_keys` reached its cap; every string operand without a
    /// runtime path is then treated as sensitive.
    pub sensitive_keys_overflowed: bool,
    /// Leaf values written into a partial-object rule's result by a
    /// multi-key or multi-value head (`ObjectDeepSet`), with where each was
    /// read from, so a report can redact them like emitted values. Kept apart
    /// from `emission_outcomes`, which partial evaluation reads.
    pub deep_object_leaves: Vec<DeepObjectLeaf>,
    /// Materialization scratch: nested-secret sanitization results for
    /// collection values, keyed by their shared allocation (see
    /// `causality_report::redact_nested_secrets_cached`).
    pub(crate) nested_secret_cache: core::cell::RefCell<NestedSecretCache>,
}

/// Nested-secret sanitization results by container allocation address. Each
/// entry holds a clone of its key value, so the address stays allocated (and
/// cannot be reused by another value) for as long as the entry exists.
pub(crate) type NestedSecretCache = alloc::collections::BTreeMap<usize, (Value, Option<Value>)>;

/// A leaf value a multi-key or multi-value partial-object head wrote.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct DeepObjectLeaf {
    /// Rule index in `Program::rule_infos`.
    pub rule_index: u16,
    /// Index of the leaf value in `captured_values`.
    pub value_idx: Option<ValueIdx>,
    /// Runtime provenance of the leaf value, when it was read from data.
    pub value_path: Option<String>,
}

/// Maximum number of recorded sensitive pair-value paths.
pub const MAX_SENSITIVE_VALUE_PATHS: usize = 1024;

impl EvaluationTrace {
    pub fn new() -> Self {
        Self::default()
    }

    /// Clear the trace for reuse.
    pub fn clear(&mut self) {
        self.condition_outcomes.clear();
        self.captured_values.clear();
        self.loop_stats.clear();
        self.rule_outcomes.clear();
        self.emission_outcomes.clear();
        self.assumptions.clear();
        self.warnings.clear();
        self.next_iteration_id = 0;
        self.next_conjunction_id = 0;
        self.next_negation_scope_id = 0;
        self.negation_scope_stack.clear();
        self.definitive_result = false;
        self.sensitive_value_paths.clear();
        self.sensitive_value_paths_overflowed = false;
        self.sensitive_keys.clear();
        self.sensitive_keys_overflowed = false;
        self.deep_object_leaves.clear();
        self.nested_secret_cache.get_mut().clear();
    }

    /// Record a leaf a multi-key partial-object head wrote.
    pub fn record_deep_object_leaf(
        &mut self,
        rule_index: u16,
        value: Value,
        value_path: Option<String>,
    ) {
        let value_idx = self.capture_value(value);
        self.deep_object_leaves.push(DeepObjectLeaf {
            rule_index,
            value_idx,
            value_path,
        });
    }

    /// Record `key` as a key of a sensitive collection.
    pub fn record_sensitive_key(&mut self, key: &Value) {
        if self.sensitive_keys.contains(key) {
            return;
        }
        if self.sensitive_keys.len() >= MAX_SENSITIVE_VALUE_PATHS {
            self.sensitive_keys_overflowed = true;
            return;
        }
        self.sensitive_keys.insert(key.clone());
    }

    /// Record `path` as holding the `value` of a sensitive name/value pair.
    pub fn record_sensitive_value_path(&mut self, path: &str) {
        if self.sensitive_value_paths.contains(path) {
            return;
        }
        if self.sensitive_value_paths.len() >= MAX_SENSITIVE_VALUE_PATHS {
            self.sensitive_value_paths_overflowed = true;
            return;
        }
        self.sensitive_value_paths.insert(String::from(path));
    }

    /// Returns true if the trace is empty (nothing recorded).
    pub const fn is_empty(&self) -> bool {
        self.condition_outcomes.is_empty()
            && self.loop_stats.is_empty()
            && self.rule_outcomes.is_empty()
            && self.assumptions.is_empty()
    }

    /// Capture a value and return its index.
    pub fn capture_value(&mut self, value: Value) -> Option<ValueIdx> {
        let idx = self.captured_values.len();
        let idx_u16 = u16::try_from(idx).ok()?;
        self.captured_values.push(value);
        Some(idx_u16)
    }

    /// Record a condition outcome.
    #[allow(clippy::too_many_arguments)]
    pub fn record_condition(
        &mut self,
        pc: u32,
        passed: bool,
        assumed: bool,
        actual: Option<Value>,
        actual_path: Option<String>,
        expected: Option<Value>,
        expected_path: Option<String>,
        rule_index: u16,
    ) {
        let actual_idx = actual.and_then(|v| self.capture_value(v));
        let expected_idx = expected.and_then(|v| self.capture_value(v));
        self.condition_outcomes.push(ConditionOutcome {
            pc,
            passed,
            assumed,
            actual_value_idx: actual_idx,
            actual_path,
            actual_absent: false,
            expected_value_idx: expected_idx,
            expected_path,
            loop_stat_idx: None,
            rule_index,
        });
    }

    /// Attach a loop summary to the most recently recorded condition outcome.
    pub fn attach_loop_stat_to_last_condition(
        &mut self,
        pc: u32,
        total_iterations: u32,
        success_count: u32,
        sample_key: Option<Value>,
        sample_value: Option<Value>,
    ) {
        let key_idx = sample_key.and_then(|v| self.capture_value(v));
        let val_idx = sample_value.and_then(|v| self.capture_value(v));
        let loop_idx = self.loop_stats.len();
        let Some(loop_idx_u16) = u16::try_from(loop_idx).ok() else {
            return;
        };

        let emissions_before_exit = self.emissions_recorded();
        self.loop_stats.push(LoopStat {
            pc,
            anchor_condition_idx: self
                .condition_outcomes
                .len()
                .checked_sub(1)
                .and_then(|idx| u32::try_from(idx).ok()),
            total_iterations,
            success_count,
            sample_key: key_idx,
            sample_value: val_idx,
            collection_path: None,
            emissions_before_exit,
            enclosing_iteration: None,
            sample_path: None,
        });

        if let Some(outcome) = self.condition_outcomes.last_mut() {
            outcome.loop_stat_idx = Some(loop_idx_u16);
        }
    }

    /// Record a loop completion. `collection_path` is the runtime
    /// provenance of the iterated collection, when known;
    /// `enclosing_iteration` is the iteration of the innermost loop of the
    /// same rule frame that was running when this loop started.
    #[allow(clippy::too_many_arguments)]
    pub fn record_loop(
        &mut self,
        pc: u32,
        anchor_condition_idx: Option<u32>,
        total_iterations: u32,
        success_count: u32,
        sample_key: Option<Value>,
        sample_value: Option<Value>,
        collection_path: Option<crate::Rc<str>>,
        enclosing_iteration: Option<u32>,
        sample_path: Option<crate::Rc<str>>,
    ) {
        let key_idx = sample_key.and_then(|v| self.capture_value(v));
        let val_idx = sample_value.and_then(|v| self.capture_value(v));
        let emissions_before_exit = self.emissions_recorded();
        self.loop_stats.push(LoopStat {
            pc,
            anchor_condition_idx,
            total_iterations,
            success_count,
            sample_key: key_idx,
            sample_value: val_idx,
            collection_path,
            emissions_before_exit,
            enclosing_iteration,
            sample_path,
        });
    }

    fn emissions_recorded(&self) -> u32 {
        u32::try_from(self.emission_outcomes.len()).unwrap_or(u32::MAX)
    }

    /// Record a rule definition outcome.
    pub fn record_rule_outcome(
        &mut self,
        rule_index: u16,
        definition_index: u16,
        succeeded: bool,
        result_value: Option<Value>,
    ) {
        let result_idx = result_value.and_then(|v| self.capture_value(v));
        let conditions_recorded = u32::try_from(self.condition_outcomes.len()).unwrap_or(u32::MAX);
        self.rule_outcomes.push(RuleOutcome {
            rule_index,
            definition_index,
            succeeded,
            result_value_idx: result_idx,
            is_summary: false,
            result_path: None,
            conditions_recorded,
            assumption_dependent: false,
        });
    }

    /// Record a rule-level summary outcome (per-rule rather than per-definition).
    ///
    /// This is recorded once at the end of a rule's evaluation, carrying the
    /// final accumulated result value.  Per-definition outcomes are recorded
    /// separately via `record_rule_outcome` so that `rule.definitions[]`
    /// contains one entry per definition body that ran.
    pub fn record_rule_summary(
        &mut self,
        rule_index: u16,
        succeeded: bool,
        result_value: Option<Value>,
    ) {
        let result_idx = result_value.and_then(|v| self.capture_value(v));
        let conditions_recorded = u32::try_from(self.condition_outcomes.len()).unwrap_or(u32::MAX);
        self.rule_outcomes.push(RuleOutcome {
            rule_index,
            definition_index: 0,
            succeeded,
            result_value_idx: result_idx,
            is_summary: true,
            result_path: None,
            conditions_recorded,
            assumption_dependent: false,
        });
    }

    /// Record a partial-set emission, the body-window conditions and the loop
    /// iterations active at the time.
    pub fn record_emission(
        &mut self,
        rule_index: u16,
        definition_index: u16,
        condition_start_index: u32,
        condition_end_index: u32,
        value: Value,
        active_iterations: Vec<u32>,
    ) {
        let value_idx = self.capture_value(value);
        self.emission_outcomes.push(EmissionOutcome {
            rule_index,
            definition_index,
            condition_start_index,
            condition_end_index,
            value_idx,
            active_iterations,
            value_path: None,
        });
    }

    /// Record an assumption from unknown input handling.
    #[allow(clippy::too_many_arguments)]
    pub fn record_assumption(
        &mut self,
        kind: AssumptionKind,
        input_path: String,
        condition_text: String,
        pc: u32,
        operator: Option<String>,
        assumed_value: Option<Value>,
        rule_index: u16,
        definition_index: u16,
        iteration_index: Option<u32>,
        conjunction_id: u32,
        call_chain: Vec<CallFrame>,
    ) {
        // Pick up the current negation scope (if any) from the stack.
        let negation_scope_id = self.negation_scope_stack.last().copied();
        self.assumptions.push(Assumption {
            kind,
            input_path,
            condition_text,
            pc,
            operator,
            builtin_name: None,
            assumed_value,
            assumed_value_path: None,
            rule_index,
            definition_index,
            iteration_index,
            conjunction_id,
            negation_scope_id,
            owned_negation_scope_id: None,
            data_lookup_context: None,
            orphaned: false,
            call_chain,
        });
    }

    /// Push a negation scope — called when entering a `not` body.
    /// Returns the scope ID so the caller can record it on the
    /// `NegationHolds` assumption later.
    pub fn push_negation_scope(&mut self) -> u32 {
        let id = self.next_negation_scope_id;
        self.next_negation_scope_id = id.saturating_add(1);
        self.negation_scope_stack.push(id);
        id
    }

    /// Pop the current negation scope.
    pub fn pop_negation_scope(&mut self) {
        self.negation_scope_stack.pop();
    }

    /// Resolve a captured value by index.
    pub fn get_value(&self, idx: ValueIdx) -> Option<&Value> {
        self.captured_values.get(usize::from(idx))
    }
}
