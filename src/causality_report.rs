// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]

//! Materialization of causality reports from static metadata + runtime trace.
//!
//! This module combines the compile-time `StaticConditionInfo` from
//! [`crate::static_provenance`] with the runtime [`crate::evaluation_trace::EvaluationTrace`]
//! to produce the final [`CausalityReport`] JSON output.

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use serde::Serialize;

use crate::evaluation_trace::{
    AssumptionKind, ConditionMode, ConditionOutcome, EvaluationTrace, ExplanationDetail,
    ExplanationScope, ExplanationSettings, RuleOutcome, ValueMode,
};
use crate::rvm::program::Program;
use crate::rvm::Instruction;
use crate::static_provenance::{Provenance, ProvenanceRoot};
use crate::value::Value;

// ---------------------------------------------------------------------------
// Redaction
// ---------------------------------------------------------------------------

/// Field names that are redacted when value_mode is Redacted.
const SENSITIVE_FIELDS: &[&str] = &[
    "password",
    "secret",
    "token",
    "api_key",
    "apikey",
    "api-key",
    "jwt",
    "credential",
    "private_key",
    "privatekey",
    "access_key",
    "accesskey",
];

fn should_redact_path(provenance: Option<&Provenance>) -> bool {
    let Some(prov) = provenance else {
        return false;
    };
    for seg in &prov.segments {
        if let crate::static_provenance::Segment::Field(ref name) = *seg {
            let lower = str::to_ascii_lowercase(name);
            for sensitive in SENSITIVE_FIELDS {
                if lower.contains(sensitive) {
                    return true;
                }
            }
        }
    }
    false
}

fn should_redact_runtime_path(path: Option<&str>) -> bool {
    let Some(path) = path else {
        return false;
    };

    let lower = path.to_ascii_lowercase();
    SENSITIVE_FIELDS.iter().any(|field| lower.contains(field))
}

fn assumed_input_path_for_pc(trace: &EvaluationTrace, pc: u32) -> Option<String> {
    trace
        .assumptions
        .iter()
        .find(|assumption| assumption.pc == pc)
        .map(|assumption| assumption.input_path.clone())
}

fn operand_provenance_for_output(
    runtime_path: Option<&str>,
    static_provenance: Option<&Provenance>,
    outcome: &ConditionOutcome,
    trace: &EvaluationTrace,
) -> Option<String> {
    if let Some(path) = runtime_path {
        return Some(path.to_string());
    }

    if outcome.assumed
        && matches!(
            static_provenance.map(|provenance| &provenance.root),
            Some(ProvenanceRoot::RuleResult { .. })
        )
    {
        if let Some(path) = assumed_input_path_for_pc(trace, outcome.pc) {
            return Some(path);
        }
    }

    static_provenance.map(|provenance| provenance.to_string())
}

// ---------------------------------------------------------------------------
// Output types
// ---------------------------------------------------------------------------

/// Top-level causality report.
#[derive(Debug, Clone, Serialize)]
pub struct CausalityReport {
    /// The value returned by the evaluated query.
    pub query_result: Value,
    /// Per-rule explanation details.
    pub rules: Vec<RuleExplanation>,
    /// Assumptions made when unknown input handling was active.
    pub assumptions: Vec<AssumptionRecord>,
}

/// Explanation for a single rule.
#[derive(Debug, Clone, Serialize)]
pub struct RuleExplanation {
    /// Fully-qualified rule name, e.g. `"data.test.allow"`.
    pub name: String,
    /// Rule type.
    #[serde(rename = "type")]
    pub rule_type: String,
    /// Final result of the rule.
    pub result: Value,
    /// Per-emission explanations for partial-set rules.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub emissions: Vec<EmissionExplanation>,
    /// Explanations for each definition that was evaluated.
    pub definitions: Vec<DefinitionExplanation>,
}

/// Explanation for a single emitted partial-set value.
#[derive(Debug, Clone, Serialize)]
pub struct EmissionExplanation {
    /// Stable 0-based index of this materialized emission within the rule.
    pub index: usize,
    /// Definition that produced this value.
    pub definition_index: u16,
    /// The emitted value.
    pub result: Value,
    /// Conditions active when the value was emitted.
    pub conditions: Vec<ConditionExplanation>,
}

/// Explanation for a single rule definition body.
#[derive(Debug, Clone, Serialize)]
pub struct DefinitionExplanation {
    /// 0-based definition index within the rule.
    pub index: u16,
    /// Whether this definition succeeded or failed.
    pub outcome: String,
    /// Source location of the definition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// Condition evaluations within this definition.
    pub conditions: Vec<ConditionExplanation>,
}

/// A single condition evaluation.
#[derive(Debug, Clone, Serialize)]
pub struct ConditionExplanation {
    /// Source text of the condition.
    pub text: String,
    /// `"success"`, `"failure"`, or `"assumed"`.
    pub outcome: String,
    /// Source location.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// Condition kind (comparison, existence, truthiness, etc.).
    pub kind: String,
    /// Operator (for comparisons).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<String>,
    /// Left / actual operand.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub left: Option<OperandExplanation>,
    /// Right / expected operand.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub right: Option<OperandExplanation>,
    /// Loop or quantifier witness summary, when available.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub witness: Option<LoopWitnessExplanation>,
    /// For binding conditions (`:=`): the variable name being bound.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binding_name: Option<String>,
    /// For Builtin kind: the builtin function name (`"startswith"`, `"endswith"`,
    /// `"contains"`). Populated only when `kind == "builtin"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub builtin_name: Option<String>,
    /// Orthogonal modifier: `true` when the condition's truth is inverted (e.g.
    /// `not X == Y` emits `kind: "comparison", negated: true`, and
    /// `not startswith(X, "foo")` emits `kind: "builtin", negated: true`). Omitted
    /// from serialized output when `false`, so positive conditions keep the same
    /// shape they had before this field existed.
    #[serde(default, skip_serializing_if = "is_false")]
    pub negated: bool,
    /// For truthiness conditions whose backing register was written by a
    /// `CallRule` (i.e. the customer wrote `not _helper(x)` or bare
    /// `_helper(x)` as a guard), this carries the helper's evaluated inner
    /// conditions structurally so consumers can render "Violation caused by:
    /// …" inline. Populated at materialize time by walking chronological
    /// `condition_outcomes` between the `CallRule` and outer `Guard`,
    /// filtered by `rule_index == helper_idx`. Omitted from serialized
    /// output when empty. Bounded by the `MAX_HELPER_DEPTH` recursion guard for
    /// nested helpers.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub helper_conditions: Vec<ConditionExplanation>,
}

/// Serde skip helper: omit the field when the boolean is `false`.
const fn is_false(b: &bool) -> bool {
    !*b
}

/// Witness summary for a loop-backed condition.
#[derive(Debug, Clone, Serialize)]
pub struct LoopWitnessExplanation {
    pub total_iterations: u32,
    pub success_count: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sample_key: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sample_value: Option<Value>,
}

/// An operand value with optional provenance.
#[derive(Debug, Clone, Serialize)]
pub struct OperandExplanation {
    /// The runtime value (may be redacted).
    pub value: Value,
    /// Data path, e.g. `"input.role"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub provenance: Option<String>,
    /// Whether the value was redacted.
    pub redacted: bool,
    /// Fully-qualified Azure Policy alias name this value was compiled from,
    /// e.g. `"Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly"`.
    /// Lets a consumer map straight to the alias's ARM `defaultPath` instead
    /// of inverting the (lower-cased, `properties`-flattened) `provenance`
    /// path above. Absent for non-Azure-Policy conditions and for values not
    /// compiled from an alias.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_alias: Option<String>,
}

/// Source location.
#[derive(Debug, Clone, Serialize)]
pub struct SourceLocation {
    pub file: String,
    pub row: usize,
    pub col: usize,
}

/// A recorded assumption for the output.
#[derive(Debug, Clone, Serialize)]
pub struct AssumptionRecord {
    /// Kind of assumption.
    pub kind: String,
    /// Input path that was assumed.
    pub input_path: String,
    /// Condition text that was assumed to hold.
    pub assumed_holds: String,
    /// The comparison operator (e.g. "==", "!="), if applicable.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<String>,
    /// The non-input value that was compared against.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assumed_value: Option<Value>,
    /// Source location.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
}

// ---------------------------------------------------------------------------
// Partial Evaluation Output
// ---------------------------------------------------------------------------

/// A single condition in a PE residual query.
#[derive(Debug, Clone, Serialize)]
pub struct ResidualCondition {
    /// The condition text, e.g. `"input.document.status == \"public\""`.
    pub condition: String,
    /// The comparison operator, e.g. `"=="`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<String>,
    /// The operator as the policy author wrote it, when it differs from the
    /// normalized symbol in `operator` (Azure Policy's `notEquals` vs `!=`).
    /// Mirrors `ConditionExplanation::builtin_name` so a consumer can render
    /// residuals in the authoring language without parsing source text.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub builtin_name: Option<String>,
    /// The input path that is unknown, e.g. `"input.document.status"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub input_path: Option<String>,
    /// The concrete value being compared against.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value: Option<Value>,
    /// Kind of assumption.
    pub kind: String,
    /// For `negation_holds` conditions: the inner conditions that the negation
    /// wraps.  Semantics: "NOT (all of negated_conditions hold simultaneously)".
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub negated_conditions: Vec<ResidualCondition>,
    /// Fully-qualified rule name that produced this residual condition,
    /// e.g. `"data.bicep.deny"`.  Lets consumers attribute a disjunct back
    /// to the rule (and rule definition) that contributed it without
    /// re-running PE per rule.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_rule: Option<String>,
    /// Source file where the condition appears, e.g. `"policy.rego"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_file: Option<String>,
    /// 1-based source line for the condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_row: Option<u32>,
    /// 1-based source column for the condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_col: Option<u32>,
    /// 1-based source line of the FIRST instruction of the rule body
    /// (definition) that produced this condition.  Mirrors the value reported
    /// by `DefinitionExplanation.location.row` in the causality report, so
    /// consumers can exact-match a PE residual conjunct to the rule body it
    /// came from — including the multi-body same-name rule case.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_rule_start_row: Option<u32>,
    /// Calling rule frames, outermost first, present when this condition was
    /// recorded inside a helper that another rule invoked. `call_chain[0]` is
    /// the rule that owns the residual at any call depth, which is the key a
    /// consumer joins a residual back to its violation on; `source_rule`
    /// continues to name the callee that recorded it, and is never duplicated
    /// into the chain. Absent for a condition recorded directly in a rule body.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub call_chain: Vec<CallFrameInfo>,
}

/// One calling rule frame for a residual recorded inside a helper.
#[derive(Debug, Clone, Serialize)]
pub struct CallFrameInfo {
    /// Fully-qualified name of the calling rule, e.g. `"data.bicep.deny"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule: Option<String>,
    /// Source file declaring the calling rule's body. Carried alongside the
    /// name and row because a helper may live in a different file from its
    /// caller, and a consumer that scopes a body match by file would
    /// otherwise fail to attribute the residual.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule_file: Option<String>,
    /// 1-based line of the first instruction of the calling rule's active
    /// body. Carried because a name alone cannot distinguish two bodies of a
    /// same-named rule, and a consumer that matches bodies needs both.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule_start_row: Option<u32>,
    /// 1-based line of the call site inside this frame.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub call_row: Option<u32>,
}

/// Result of partial evaluation.
#[derive(Debug, Clone, Serialize)]
pub struct PartialEvalResult {
    /// The query result: `true`, `false`, or `null` (for undefined).
    pub result: Value,
    /// DNF residual queries: outer vec is OR, inner vec is AND.
    pub residual_queries: Vec<Vec<ResidualCondition>>,
    /// Warnings or informational messages.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<String>,
}

/// Produce a [`PartialEvalResult`] from a program and its evaluation trace.
pub fn materialize_pe(
    program: &Program,
    trace: &EvaluationTrace,
    query_result: Value,
) -> PartialEvalResult {
    // If the result is fully determined (at least one definition succeeded
    // without any assumptions), skip residual computation.
    if trace.definitive_result {
        let result = match query_result {
            Value::Undefined => Value::Null,
            other => other,
        };
        return PartialEvalResult {
            result,
            residual_queries: Vec::new(),
            warnings: trace.warnings.clone(),
        };
    }

    use alloc::collections::BTreeMap;

    // -----------------------------------------------------------------------
    // 1. Collect negation-scoped inner assumptions into a side-map.
    //    Assumptions with `negation_scope_id = Some(id)` are inner conditions
    //    of a `not` body.  They should NOT appear as top-level disjunct
    //    conditions; instead they are attached to the parent NegationHolds
    //    condition that shares the same scope id.
    // -----------------------------------------------------------------------
    let mut negation_inner: BTreeMap<u32, Vec<ResidualCondition>> = BTreeMap::new();

    // Group assumptions by (conjunction_id, iteration_index) to form disjuncts.
    // Each unique combination produces one conjunction (AND) in the DNF output.
    let mut disjunct_map: BTreeMap<(u32, Option<u32>), Vec<ResidualCondition>> = BTreeMap::new();

    // First pass: collect inner-negation assumptions into negation_inner.
    for a in &trace.assumptions {
        // An assumption is orphaned when its enclosing definition (or any
        // enclosing definition on the call stack) failed to emit / assign
        // a value, meaning the assumption cannot have caused any observable
        // effect.
        if a.orphaned {
            continue;
        }
        if let Some(neg_scope) = a.negation_scope_id {
            let cond = assumption_to_residual(a, program);
            negation_inner.entry(neg_scope).or_default().push(cond);
        }
    }

    // Second pass: build disjuncts from top-level (non-negation-inner) assumptions.
    for a in &trace.assumptions {
        // Skip orphaned assumptions (see comment on first pass above).
        if a.orphaned {
            continue;
        }
        // Skip assumptions that belong inside a negation body — they will be
        // attached to the NegationHolds parent below.
        if a.negation_scope_id.is_some() {
            continue;
        }

        let key = (a.conjunction_id, a.iteration_index);

        // For NegationHolds: single condition with inner children.
        if a.kind == AssumptionKind::NegationHolds {
            let mut cond = assumption_to_residual(a, program);
            if let Some(scope_id) = a.owned_negation_scope_id {
                if let Some(mut inner) = negation_inner.remove(&scope_id) {
                    attach_nested_negation_inner(&mut inner, &mut negation_inner);
                    cond.negated_conditions = inner;
                }
            }
            disjunct_map.entry(key).or_default().push(cond);
            continue;
        }

        // Try data-key inversion (may produce multiple conditions).
        let inverted = assumption_to_residual_conditions(a, program);
        if inverted.len() > 1 {
            // Multiple matching keys → each becomes a separate disjunct
            // so the overall result is OR(key1, key2, ...).
            // We tag them with synthetic iteration indices to separate them.
            for (i, cond) in inverted.into_iter().enumerate() {
                let offset = u32::try_from(i).unwrap_or(u32::MAX);
                let split_key = (
                    key.0,
                    Some(
                        key.1
                            .unwrap_or(0)
                            .wrapping_add(1000_u32.wrapping_add(offset)),
                    ),
                );
                disjunct_map.entry(split_key).or_default().push(cond);
            }
        } else {
            for cond in inverted {
                disjunct_map.entry(key).or_default().push(cond);
            }
        }
    }

    // Deduplicate conditions within each disjunct.
    // Also drop empty `negation_holds` placeholders (PE-2): when a rule
    // fires concretely the recorded NegationHolds assumption may carry no
    // input path, no operator, and no inner conditions.  Such a placeholder
    // provides no information to consumers and prevents the disjunct from
    // collapsing to an empty (always-true) clause.
    //
    // The filter recurses into `negated_conditions[]` so empty placeholders
    // nested inside another `negation_holds` are also dropped;
    // `attach_nested_negation_inner` above assigns the inner arrays but
    // doesn't filter them.
    let residual_queries: Vec<Vec<ResidualCondition>> = disjunct_map
        .into_values()
        .filter_map(|mut conds| {
            conds.dedup_by(|a, b| a.condition == b.condition && a.operator == b.operator);
            filter_empty_placeholders_recursive(&mut conds);
            if conds.is_empty() {
                None
            } else {
                Some(conds)
            }
        })
        .collect();

    let result = match query_result {
        Value::Undefined => Value::Null,
        other => other,
    };

    PartialEvalResult {
        result,
        residual_queries,
        warnings: trace.warnings.clone(),
    }
}

/// Format a `Value` for display in condition text.
fn format_value(v: &Value) -> alloc::string::String {
    match v {
        Value::String(s) => alloc::format!("\"{}\"", s),
        Value::Null => "null".into(),
        Value::Bool(b) => alloc::format!("{b}"),
        Value::Number(n) => alloc::format!("{:?}", n),
        _ => alloc::format!("{:?}", v),
    }
}

/// Convert an `Assumption` to a `ResidualCondition`.
/// When the assumption has a `data_lookup_context`, inverts the lookup:
/// instead of `data.perms[input.role] == "write"`, produces one or more
/// conditions like `input.role == "admin"`.
fn assumption_to_residual_conditions(
    a: &crate::evaluation_trace::Assumption,
    program: &Program,
) -> Vec<ResidualCondition> {
    let (source_rule, source_file, source_row, source_col, source_rule_start_row) =
        source_attribution(a, program);

    // Check for data-key inversion.
    if let (Some(ref ctx), Some(ref cmp_value), Some(ref op)) =
        (&a.data_lookup_context, &a.assumed_value, &a.operator)
    {
        if let Value::Object(ref obj) = ctx.data_object {
            let matching_keys: Vec<&Value> = obj
                .iter()
                .filter(|(_, v)| match op.as_str() {
                    "==" => *v == cmp_value,
                    "!=" => *v != cmp_value,
                    _ => false,
                })
                .map(|(k, _)| k)
                .collect();

            if !matching_keys.is_empty() {
                return matching_keys
                    .into_iter()
                    .map(|key| {
                        let inverted_op = match op.as_str() {
                            "!=" => "!=", // preserve != semantics
                            _ => "==",
                        };
                        ResidualCondition {
                            condition: alloc::format!(
                                "{} {} {}",
                                ctx.key_input_path,
                                inverted_op,
                                format_value(key),
                            ),
                            operator: Some(inverted_op.to_string()),
                            // Data-key inversion rewrites the operator, so the
                            // authored form no longer describes this condition.
                            builtin_name: None,
                            input_path: Some(ctx.key_input_path.clone()),
                            value: Some(key.clone()),
                            kind: "condition_holds".to_string(),
                            negated_conditions: Vec::new(),
                            source_rule: source_rule.clone(),
                            source_file: source_file.clone(),
                            source_row,
                            source_col,
                            source_rule_start_row,
                            call_chain: call_chain_attribution(a, program),
                        }
                    })
                    .collect();
            }
        }
    }

    // Default: no inversion, return single condition.
    alloc::vec![assumption_to_residual(a, program)]
}

/// Convert an `Assumption` to a single `ResidualCondition` (no inversion).
fn assumption_to_residual(
    a: &crate::evaluation_trace::Assumption,
    program: &Program,
) -> ResidualCondition {
    let kind_str = match a.kind {
        AssumptionKind::Exists => "exists",
        AssumptionKind::ConditionHolds => "condition_holds",
        AssumptionKind::CollectionExists => "collection_exists",
        AssumptionKind::NegationHolds => "negation_holds",
    };
    let (source_rule, source_file, source_row, source_col, source_rule_start_row) =
        source_attribution(a, program);
    ResidualCondition {
        condition: residual_condition_text(a, program),
        operator: a.operator.clone(),
        builtin_name: a.builtin_name.clone(),
        // Strip the trailing `[_]` iteration marker from `input_path` on
        // `exists` and `condition_holds` kinds. The `[_]` originates in
        // `rvm/vm/loops.rs`'s phantom-iteration setup (`element_path = base + "[_]"`
        // tainting the iterator's value-register provenance) and propagates
        // through Guard/comparison assumption recording. It's an engine-internal
        // iterator variable placeholder with no meaning to a policy author.
        // `collection_exists` is already clean (recorded pre-taint from the base
        // path); `negation_holds` carries an empty `input_path`.
        input_path: if a.input_path.is_empty() {
            None
        } else {
            Some(match kind_str {
                "exists" | "condition_holds" => strip_iteration_suffix(&a.input_path),
                _ => a.input_path.clone(),
            })
        },
        value: a.assumed_value.clone(),
        kind: kind_str.to_string(),
        negated_conditions: Vec::new(),
        source_rule,
        source_file,
        source_row,
        source_col,
        source_rule_start_row,
        call_chain: call_chain_attribution(a, program),
    }
}

/// Strip a trailing `[_]` iterator placeholder from an input path.
/// Returns the base collection path when the suffix is present; otherwise
/// clones the input unchanged.
fn strip_iteration_suffix(path: &str) -> String {
    path.strip_suffix("[_]").unwrap_or(path).to_string()
}

/// Name a program that has no rule structure, from the compiler's definition
/// metadata. Shared by causality's synthetic rule and PE's residual source
/// attribution so a consumer can join the two on the same string.
fn ruleless_program_name(program: &Program) -> alloc::string::String {
    ["display_name", "policy_name", "policy_id"]
        .iter()
        .find_map(|key| {
            program
                .metadata
                .annotations
                .get(*key)
                .and_then(|v| v.as_string().ok())
                .map(|s| s.as_ref().to_string())
        })
        .unwrap_or_else(|| alloc::string::String::from("policy"))
}

/// `(rule_name, source_file, row, col, rule_start_row)` for an assumption.
type SourceAttribution = (
    Option<String>,
    Option<String>,
    Option<u32>,
    Option<u32>,
    Option<u32>,
);

/// Look up (rule_name, source_file, row, col, rule_start_row) for an assumption.
fn source_attribution(
    a: &crate::evaluation_trace::Assumption,
    program: &Program,
) -> SourceAttribution {
    let rule_info = program.rule_infos.get(usize::from(a.rule_index));
    // A rule-less program (Azure Policy) has no `RuleInfo`, so name it the same
    // way causality names its synthetic rule — that string is the join key a
    // consumer uses to match a residual to its causality violation.
    let rule_name = match rule_info {
        Some(info) => Some(info.name.clone()),
        None if program.rule_infos.is_empty() => Some(ruleless_program_name(program)),
        None => None,
    };
    let pc_usize: usize = a.pc.try_into().unwrap_or(0);
    let (file, row, col) = program
        .instruction_spans
        .get(pc_usize)
        .and_then(Option::as_ref)
        .map(|span| {
            let file = program
                .sources
                .get(span.source_index)
                .map(|s| s.name.clone())
                .unwrap_or_default();
            (
                Some(file),
                Some(u32::try_from(span.line).unwrap_or(u32::MAX)),
                Some(u32::try_from(span.column).unwrap_or(u32::MAX)),
            )
        })
        .unwrap_or((None, None, None));
    // Mirror `materialize_definitions`: the rule-body row is the line of the
    // FIRST instruction of `RuleInfo.definitions[definition_index]`. Causality
    // already reports this as `DefinitionExplanation.location.row`, so a
    // consumer can join PE residual conjuncts to causality definitions by
    // exact equality on (rule_name, rule_start_row) — critical for the
    // multi-body same-name rule case.
    let rule_start_row = rule_body_start_row(program, a.rule_index, a.definition_index);
    (rule_name, file, row, col, rule_start_row)
}

/// 1-based line of the first instruction of a rule definition's body.
///
/// Shared by the recording rule's own attribution and by each calling frame
/// in `call_chain`, so both sides of a consumer's body-level join are computed
/// the same way rather than by two implementations that could drift.
fn rule_body_start_row(program: &Program, rule_index: u16, definition_index: u16) -> Option<u32> {
    rule_body_span(program, rule_index, definition_index)
        .map(|span| u32::try_from(span.line).unwrap_or(u32::MAX))
}

/// Span of the first instruction of a rule definition's body.
fn rule_body_span(
    program: &Program,
    rule_index: u16,
    definition_index: u16,
) -> Option<crate::rvm::program::SpanInfo> {
    program
        .rule_infos
        .get(usize::from(rule_index))
        .and_then(|info| info.definitions.get(usize::from(definition_index)))
        .and_then(|def_pcs| def_pcs.first().copied())
        .and_then(|first_pc| {
            let idx = usize::try_from(first_pc).unwrap_or(0);
            program.instruction_spans.get(idx).cloned()
        })
        .flatten()
}

/// Name of the source file a span belongs to.
fn span_source_name(program: &Program, span: &crate::rvm::program::SpanInfo) -> Option<String> {
    program
        .sources
        .get(span.source_index)
        .map(|source| source.name.clone())
}

/// 1-based source line for an instruction.
fn instruction_row(program: &Program, pc: u32) -> Option<u32> {
    let idx = usize::try_from(pc).unwrap_or(0);
    program
        .instruction_spans
        .get(idx)
        .and_then(Option::as_ref)
        .map(|span| u32::try_from(span.line).unwrap_or(u32::MAX))
}

/// Resolve the recorded calling frames into names, files and rows, outermost
/// first.
fn call_chain_attribution(
    a: &crate::evaluation_trace::Assumption,
    program: &Program,
) -> Vec<CallFrameInfo> {
    a.call_chain
        .iter()
        .map(|frame| {
            let body_span = rule_body_span(program, frame.rule_index, frame.definition_index);
            CallFrameInfo {
                rule: program
                    .rule_infos
                    .get(usize::from(frame.rule_index))
                    .map(|info| info.name.clone()),
                rule_file: body_span
                    .as_ref()
                    .and_then(|span| span_source_name(program, span)),
                rule_start_row: body_span
                    .as_ref()
                    .map(|span| u32::try_from(span.line).unwrap_or(u32::MAX)),
                call_row: instruction_row(program, frame.call_pc),
            }
        })
        .collect()
}

/// Render a residual's condition text for display.
///
/// For a condition recorded inside a helper, the raw text is the helper's
/// *definition* — rule head plus formal parameter names — which describes the
/// helper rather than the check the caller actually requested. Reuse the
/// causality path's helper-body rewriting to drop the head and substitute the
/// caller's literal arguments, so both explanation surfaces phrase a
/// helper-gated condition the same way. A non-literal argument leaves the
/// parameter name in place rather than inventing a value.
fn residual_condition_text(a: &crate::evaluation_trace::Assumption, program: &Program) -> String {
    let raw = strip_trailing_comment(&a.condition_text);
    let Some(innermost) = a.call_chain.last() else {
        return raw;
    };
    // `extract_helper_arg_substitutions` locates the call by looking at the
    // instruction *before* the pc it is given, so hand it the slot after the
    // call site.
    let after_call_pc = usize::try_from(innermost.call_pc)
        .unwrap_or(0)
        .saturating_add(1);
    let substitutions = extract_helper_arg_substitutions(after_call_pc, a.rule_index, program);
    rewrite_helper_body_text(&raw, &substitutions)
}

/// Strip a trailing Rego comment (`# ...`) from a rendered condition string,
/// preserving the meaningful expression text.  Defensive against quoted
/// `#` characters: only strips if the `#` is outside any string literal.
fn strip_trailing_comment(text: &str) -> String {
    let mut in_string: Option<char> = None;
    let mut escape = false;
    let bytes = text.as_bytes();
    for (i, ch) in text.char_indices() {
        if escape {
            escape = false;
            continue;
        }
        match in_string {
            Some(q) => {
                if ch == '\\' {
                    escape = true;
                } else if ch == q {
                    in_string = None;
                }
            }
            None => {
                if ch == '"' || ch == '\'' {
                    in_string = Some(ch);
                } else if ch == '#' {
                    let _ = bytes;
                    return text[..i].trim_end().to_string();
                }
            }
        }
    }
    text.to_string()
}

/// Returns true if `cond` is an information-free placeholder that should be
/// dropped from the DNF output.  Today this matches a `negation_holds` entry
/// with no condition text, no input path, no operator, and no inner negated
/// conditions — i.e. a frame recorded for a `not <expr>` whose inner body
/// either resolved concretely or had no input dependency to attribute (PE-2).
fn is_empty_placeholder(cond: &ResidualCondition) -> bool {
    cond.kind == "negation_holds"
        && cond.condition.is_empty()
        && cond.input_path.is_none()
        && cond.operator.is_none()
        && cond.negated_conditions.is_empty()
}

/// Recursively drop empty `negation_holds` placeholders — both at
/// the current level and inside any `negated_conditions[]` array of a
/// nested `negation_holds` frame. Order matters: recurse into children
/// FIRST so an inner `negation_holds` that becomes empty after its own
/// children are filtered also gets dropped at this level.
fn filter_empty_placeholders_recursive(conditions: &mut Vec<ResidualCondition>) {
    for cond in conditions.iter_mut() {
        if cond.kind == "negation_holds" && !cond.negated_conditions.is_empty() {
            filter_empty_placeholders_recursive(&mut cond.negated_conditions);
        }
    }
    conditions.retain(|c| !is_empty_placeholder(c));
}

/// Recursively attach inner negation conditions to any `negation_holds`
/// entries within `conditions`.
fn attach_nested_negation_inner(
    conditions: &mut [ResidualCondition],
    negation_inner: &mut alloc::collections::BTreeMap<u32, Vec<ResidualCondition>>,
) {
    for cond in conditions.iter_mut() {
        if cond.kind == "negation_holds" {
            // The inner conditions for this nested NegationHolds were
            // collected in the first pass.  We need the owned_negation_scope_id
            // but ResidualCondition doesn't carry it.  However, since we
            // consume scopes in order (BTreeMap is sorted), the next available
            // scope is the correct one for the next NegationHolds encountered.
            if let Some((&scope_id, _)) = negation_inner.iter().next() {
                if let Some(mut inner) = negation_inner.remove(&scope_id) {
                    // Recurse for deeper nesting.
                    attach_nested_negation_inner(&mut inner, negation_inner);
                    cond.negated_conditions = inner;
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Materialization
// ---------------------------------------------------------------------------

/// Produce a [`CausalityReport`] from a program and its evaluation trace.
pub fn materialize(
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
    query_result: Value,
) -> CausalityReport {
    let mut rules = materialize_rules(program, trace, settings);
    // Azure Policy compiles to a flat `main` entry point with no `CallRule`, so
    // no rule outcome is ever recorded and the conditions would be discarded.
    // Gated on `rule_infos` being empty so a Rego program, which always has
    // rules, can never take this path.
    if rules.is_empty() && program.rule_infos.is_empty() && !trace.condition_outcomes.is_empty() {
        rules.push(materialize_ruleless_program(
            program,
            trace,
            settings,
            &query_result,
        ));
    }
    let assumptions = if settings.detail == ExplanationDetail::Compact {
        Vec::new()
    } else {
        materialize_assumptions(program, trace)
    };

    CausalityReport {
        query_result,
        rules,
        assumptions,
    }
}

/// Build a single synthetic rule for a program that has no rule structure,
/// naming it from the compiler's definition metadata where available.
fn materialize_ruleless_program(
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
    query_result: &Value,
) -> RuleExplanation {
    let conditions = materialize_conditions(0, u32::MAX, program, trace, settings);
    let outcome = if conditions.iter().any(|c| c.outcome == "failure") {
        "failure"
    } else {
        "success"
    };
    let name = ruleless_program_name(program);

    RuleExplanation {
        name,
        rule_type: alloc::string::String::from("policy"),
        result: query_result.clone(),
        emissions: Vec::new(),
        definitions: alloc::vec![DefinitionExplanation {
            index: 0,
            outcome: alloc::string::String::from(outcome),
            location: None,
            conditions,
        }],
    }
}

fn materialize_rules(
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<RuleExplanation> {
    // Group rule outcomes by rule_index.
    let mut rules: Vec<RuleExplanation> = Vec::new();

    // Collect unique rule indices from outcomes.
    let mut seen_rules: Vec<u16> = Vec::new();
    for outcome in &trace.rule_outcomes {
        if !seen_rules.contains(&outcome.rule_index) {
            seen_rules.push(outcome.rule_index);
        }
    }

    for rule_idx in &seen_rules {
        let rule_info = match program.rule_infos.get(usize::from(*rule_idx)) {
            Some(info) => info,
            None => continue,
        };

        // Find the final result for this rule.
        let result = trace
            .rule_outcomes
            .iter()
            .rev()
            .find(|o| o.rule_index == *rule_idx && o.succeeded)
            .and_then(|o| o.result_value_idx)
            .and_then(|idx| trace.get_value(idx))
            .cloned()
            .unwrap_or(Value::Undefined);

        let rule_type_str = match rule_info.rule_type {
            crate::rvm::program::RuleType::Complete => "complete",
            crate::rvm::program::RuleType::PartialSet => "partial_set",
            crate::rvm::program::RuleType::PartialObject => "partial_object",
        };

        let emissions = materialize_rule_emissions(*rule_idx, rule_info, program, trace, settings);
        let definitions = if settings.scope == ExplanationScope::RuleSummary
            || (settings.detail == ExplanationDetail::Compact
                && rule_info.rule_type == crate::rvm::program::RuleType::PartialSet
                && !emissions.is_empty())
        {
            Vec::new()
        } else {
            materialize_definitions(*rule_idx, rule_info, program, trace, settings)
        };

        rules.push(RuleExplanation {
            name: rule_info.name.clone(),
            rule_type: rule_type_str.to_string(),
            result,
            emissions,
            definitions,
        });
    }

    rules
}

fn materialize_definitions(
    rule_idx: u16,
    rule_info: &crate::rvm::program::RuleInfo,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<DefinitionExplanation> {
    let mut defs: Vec<DefinitionExplanation> = Vec::new();

    let def_outcomes: Vec<&RuleOutcome> = trace
        .rule_outcomes
        .iter()
        .filter(|o| o.rule_index == rule_idx && !o.is_summary)
        .collect();

    for outcome in &def_outcomes {
        let def_idx = outcome.definition_index;

        // Get instruction range for this definition.
        let body_pcs = rule_info
            .definitions
            .get(usize::from(def_idx))
            .cloned()
            .unwrap_or_default();

        let first_pc = body_pcs.first().copied().unwrap_or(0);

        let location = get_source_location(usize::try_from(first_pc).unwrap_or(0), program);

        // Find conditions within this definition's instruction range.
        let last_pc = find_rule_return_pc(usize::try_from(first_pc).unwrap_or(0), program);

        let conditions = materialize_conditions(first_pc, last_pc, program, trace, settings);

        defs.push(DefinitionExplanation {
            index: def_idx,
            outcome: if outcome.succeeded {
                "success".to_string()
            } else {
                "failure".to_string()
            },
            location,
            conditions,
        });
    }

    defs
}

fn materialize_rule_emissions(
    rule_idx: u16,
    rule_info: &crate::rvm::program::RuleInfo,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<EmissionExplanation> {
    if rule_info.rule_type != crate::rvm::program::RuleType::PartialSet {
        return Vec::new();
    }

    if settings.scope == ExplanationScope::RuleSummary {
        return Vec::new();
    }

    let mut emissions: Vec<EmissionExplanation> = Vec::new();
    let mut seen_results: Vec<Value> = Vec::new();
    let target_emission_index = if settings.scope == ExplanationScope::SingleEmission {
        settings.emission_index
    } else {
        None
    };
    let target_emission_value = if settings.scope == ExplanationScope::SingleEmission {
        settings.emission_value.as_ref()
    } else {
        None
    };
    let mut emission_index = 0_usize;

    for emission in trace
        .emission_outcomes
        .iter()
        .filter(|outcome| outcome.rule_index == rule_idx)
    {
        let Some(result) = emission
            .value_idx
            .and_then(|idx| trace.get_value(idx))
            .cloned()
        else {
            continue;
        };

        if seen_results.contains(&result) {
            continue;
        }

        if target_emission_index.is_some_and(|target_index| emission_index != target_index) {
            seen_results.push(result);
            emission_index = emission_index.saturating_add(1);
            continue;
        }

        if target_emission_value.is_some_and(|target_value| &result != target_value) {
            seen_results.push(result);
            emission_index = emission_index.saturating_add(1);
            continue;
        }

        seen_results.push(result.clone());

        emissions.push(EmissionExplanation {
            index: emission_index,
            definition_index: emission.definition_index,
            result,
            conditions: materialize_condition_window(
                emission.condition_start_index,
                emission.condition_end_index,
                emission.rule_index,
                program,
                trace,
                settings,
            ),
        });

        emission_index = emission_index.saturating_add(1);

        if target_emission_index.is_some() {
            break;
        }
    }

    emissions
}

fn materialize_conditions(
    first_pc: u32,
    last_pc: u32,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<ConditionExplanation> {
    let relevant_outcomes = select_condition_outcomes(first_pc, last_pc, trace, settings);

    finalize_condition_explanations(
        materialize_condition_explanations(relevant_outcomes, program, trace, settings),
        settings,
        false,
    )
}

// ---------------------------------------------------------------------------
// Helper-boundary stitching
// ---------------------------------------------------------------------------

/// Maximum recursion depth when materializing nested helper bodies. Prevents
/// stack blow-up on pathological policies (mutually-recursive helpers).
const MAX_HELPER_DEPTH: usize = 8;

/// If the Guard at `outer_pc` fires on a register written by a rule call
/// (either `CallRule` for a bare rule reference, or `FunctionCall` for a
/// helper-function call — the compiler picks `FunctionCall` for helpers with
/// arguments like `_frontdoor_has_waf(resource)`), return the callee rule
/// index. Handles both the positive `_helper(x)` and negated `not _helper(x)`
/// forms (the latter has a `Not` between the call and the Guard). Returns
/// `None` otherwise.
fn detect_helper_call_at_guard(outer_pc: usize, program: &Program) -> Option<u16> {
    let guard = program.instructions.get(outer_pc)?;
    let guard_reg = match *guard {
        Instruction::Guard { register, .. } => register,
        _ => return None,
    };
    if outer_pc == 0 {
        return None;
    }
    let prev = program.instructions.get(outer_pc.saturating_sub(1))?;

    // Case 1: `_helper(x)` -- CallRule or FunctionCall writes directly to
    // the guard register.
    if let Some(rule_idx) = call_writes_to(prev, guard_reg, program) {
        return Some(rule_idx);
    }

    // Case 2: `not _helper(x)` -- Not writes to the guard register from an
    // inner register that was in turn written by CallRule/FunctionCall.
    // Small lookback window mirrors `capture_builtin_guard_operands` in
    // `dispatch.rs`.
    if let Instruction::Not { dest, operand } = *prev {
        if dest == guard_reg && outer_pc >= 2 {
            const LOOKBACK: usize = 8;
            let start = outer_pc.saturating_sub(LOOKBACK).max(1);
            let mut cur = outer_pc.saturating_sub(1);
            while cur > start {
                cur = cur.saturating_sub(1);
                let candidate = program.instructions.get(cur)?;
                if let Some(rule_idx) = call_writes_to(candidate, operand, program) {
                    return Some(rule_idx);
                }
            }
        }
    }

    None
}

/// Returns the callee rule index if `instr` is a rule-call instruction
/// (`CallRule` or `FunctionCall`) writing to `target_reg`.
fn call_writes_to(instr: &Instruction, target_reg: u8, program: &Program) -> Option<u16> {
    match *instr {
        Instruction::CallRule { dest, rule_index } if dest == target_reg => Some(rule_index),
        Instruction::FunctionCall { params_index } => {
            let params = program
                .instruction_data
                .function_call_params
                .get(usize::from(params_index))?;
            (params.dest == target_reg).then_some(params.func_rule_index)
        }
        _ => None,
    }
}

/// Walk `trace.condition_outcomes` backward from `outer_outcome_idx`,
/// collecting outcomes whose `rule_index == helper_rule_index`. Stops when it
/// hits an outcome from `outer_rule_index` (marking the boundary where helper
/// execution began). Returns them in original chronological order.
fn collect_helper_condition_outcomes(
    outer_outcome_idx: usize,
    outer_rule_index: u16,
    helper_rule_index: u16,
    trace: &EvaluationTrace,
) -> Vec<(usize, &ConditionOutcome)> {
    if outer_outcome_idx == 0 {
        return Vec::new();
    }
    let mut collected: Vec<(usize, &ConditionOutcome)> = Vec::new();
    let mut idx = outer_outcome_idx;
    while idx > 0 {
        idx = idx.saturating_sub(1);
        let Some(outcome) = trace.condition_outcomes.get(idx) else {
            break;
        };
        if outcome.rule_index == outer_rule_index {
            break;
        }
        if outcome.rule_index == helper_rule_index {
            collected.push((idx, outcome));
        }
    }
    collected.reverse();
    collected
}

/// For a truthiness outer condition on a `Guard` whose backing register was
/// written by a rule call, materialize the helper's evaluated inner
/// conditions as structural children. Returns an empty Vec
/// when no helper call is detected or the recursion depth cap is reached.
fn materialize_helper_conditions(
    outer_pc: usize,
    outer_outcome_idx: usize,
    outer_rule_index: u16,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
    depth: usize,
) -> Vec<ConditionExplanation> {
    if depth >= MAX_HELPER_DEPTH {
        return Vec::new();
    }
    let Some(helper_rule_index) = detect_helper_call_at_guard(outer_pc, program) else {
        return Vec::new();
    };
    let inner_outcomes = collect_helper_condition_outcomes(
        outer_outcome_idx,
        outer_rule_index,
        helper_rule_index,
        trace,
    );
    if inner_outcomes.is_empty() {
        return Vec::new();
    }
    let mut inner = materialize_condition_explanations_at_depth(
        inner_outcomes,
        program,
        trace,
        settings,
        depth.saturating_add(1),
    );

    // Rewrite each inner condition's `text` to just the helper body
    // expression (drop rule head `<name>(params) if `) and substitute helper
    // parameter names with the caller's argument literals extracted from the
    // FunctionCall opcode preceding `outer_pc`. Turns
    // `in_resource_group(fragment) if contains(input.deployment.resourceGroupName, fragment)`
    // into `contains(input.deployment.resourceGroupName, "prod")` so a
    // consumer can render the body without leaking helper parameter names or
    // the rule head into user-facing output.
    let substitutions = extract_helper_arg_substitutions(outer_pc, helper_rule_index, program);
    for cond in inner.iter_mut() {
        cond.text = rewrite_helper_body_text(&cond.text, &substitutions);
    }

    // Drop no-op inner entries. Helper invocation emits per-arg
    // register-binding Move outcomes which surface as `kind: "unknown"` with
    // empty `text` — they represent internal wiring (arg → param register
    // move), not authorable predicates.
    inner.retain(|c| !(c.kind == "unknown" && c.text.is_empty()));

    inner
}

/// Walk backward from `outer_pc` to locate the `FunctionCall`
/// instruction that invoked the helper. Mirrors `detect_helper_call_at_guard`:
/// the FunctionCall is either directly preceding the Guard (for `_helper(x)`),
/// or a few instructions before a `Not` (for `not _helper(x)`).
fn find_preceding_function_call_pc(outer_pc: usize, program: &Program) -> Option<usize> {
    if outer_pc == 0 {
        return None;
    }
    let prev_pc = outer_pc.saturating_sub(1);
    let prev = program.instructions.get(prev_pc)?;
    match *prev {
        Instruction::FunctionCall { .. } => Some(prev_pc),
        Instruction::Not { .. } => {
            const LOOKBACK: usize = 8;
            let start = prev_pc.saturating_sub(LOOKBACK);
            let mut cur = prev_pc;
            while cur > start {
                cur = cur.saturating_sub(1);
                if let Some(Instruction::FunctionCall { .. }) = program.instructions.get(cur) {
                    return Some(cur);
                }
            }
            None
        }
        _ => None,
    }
}

/// Build `(param_name, arg_source_literal)` pairs so
/// [`rewrite_helper_body_text`] can substitute the helper's parameter names
/// with the caller's literal argument values. Only literal arguments
/// (`Load { dest, literal_idx }` writing to the arg register) are recovered;
/// dynamic-value args leave the parameter name unsubstituted (the body text
/// stays as-is for that identifier).
fn extract_helper_arg_substitutions(
    outer_pc: usize,
    helper_rule_index: u16,
    program: &Program,
) -> Vec<(String, String)> {
    let Some(fn_call_pc) = find_preceding_function_call_pc(outer_pc, program) else {
        return Vec::new();
    };
    let Some(&Instruction::FunctionCall { params_index }) = program.instructions.get(fn_call_pc)
    else {
        return Vec::new();
    };
    let Some(params) = program
        .instruction_data
        .function_call_params
        .get(usize::from(params_index))
    else {
        return Vec::new();
    };
    let Some(rule_info) = program.rule_infos.get(usize::from(helper_rule_index)) else {
        return Vec::new();
    };
    let Some(function_info) = &rule_info.function_info else {
        return Vec::new();
    };
    let arg_registers = params.arg_registers();
    let mut substitutions: Vec<(String, String)> = Vec::new();
    for (i, param_name) in function_info.param_names.iter().enumerate() {
        let Some(&arg_reg) = arg_registers.get(i) else {
            break;
        };
        if let Some(literal_str) = find_literal_load(fn_call_pc, arg_reg, program) {
            substitutions.push((param_name.clone(), literal_str));
        }
    }
    substitutions
}

/// Walk backward from `pc` (exclusive) within a bounded window,
/// looking for a `Load { dest, literal_idx }` that wrote to `target_reg`.
/// Returns the loaded value formatted as its Rego source literal (via
/// [`format_value`]) when found. Returns `None` when the arg was not
/// populated by a simple literal load (e.g. dynamic value, chained index,
/// arithmetic result) — in which case the caller leaves the parameter
/// name unsubstituted in the body text.
fn find_literal_load(pc: usize, target_reg: u8, program: &Program) -> Option<String> {
    const LOOKBACK: usize = 32;
    let start = pc.saturating_sub(LOOKBACK);
    let mut cur = pc;
    while cur > start {
        cur = cur.saturating_sub(1);
        let instr = program.instructions.get(cur)?;
        if let Instruction::Load { dest, literal_idx } = *instr {
            if dest == target_reg {
                let literal = program.literals.get(usize::from(literal_idx))?;
                return Some(format_value(literal));
            }
        }
    }
    None
}

/// Rewrite a helper inner condition's raw source text so it renders
/// as just the body expression with parameter names substituted. Two passes:
///
/// 1. Slice past the first ` if ` boundary (the Rego rule-head/body separator)
///    to drop the helper rule declaration prefix. Absent ` if ` means the
///    text was already body-only (e.g. 0-arg helper's Guard on an inline
///    expression) and no slicing occurs.
/// 2. For each `(param, literal)` pair, do a word-boundary substitution of
///    `param` → `literal` throughout the body. Only identifier-token matches
///    are replaced; substrings inside longer identifiers or other tokens are
///    left alone.
fn rewrite_helper_body_text(text: &str, substitutions: &[(String, String)]) -> String {
    const SEPARATOR: &str = " if ";
    let body = text
        .find(SEPARATOR)
        .and_then(|pos| pos.checked_add(SEPARATOR.len()))
        .and_then(|body_start| text.get(body_start..))
        .unwrap_or(text);
    let mut current = body.to_string();
    for (param, replacement) in substitutions {
        current = substitute_identifier(&current, param, replacement);
    }
    current
}

/// Word-boundary-aware substitution used to swap helper parameter
/// names for caller-supplied argument literals in helper body text. Boundary
/// characters are ASCII identifier characters (`[A-Za-z0-9_]`); other bytes,
/// including all non-ASCII, count as a boundary. Rego parameter names are
/// ASCII identifiers by grammar, so a byte-level check is sound here.
fn substitute_identifier(text: &str, pattern: &str, replacement: &str) -> String {
    if pattern.is_empty() {
        return text.to_string();
    }
    let mut out = String::with_capacity(text.len());
    let mut cursor = 0;
    while cursor < text.len() {
        match text[cursor..].find(pattern) {
            Some(rel) => {
                let start = cursor.saturating_add(rel);
                let end = start.saturating_add(pattern.len());
                out.push_str(&text[cursor..start]);
                let left_ok = start == 0
                    || !text[..start]
                        .chars()
                        .next_back()
                        .is_some_and(is_identifier_char);
                let right_ok = end == text.len()
                    || !text[end..].chars().next().is_some_and(is_identifier_char);
                if left_ok && right_ok {
                    out.push_str(replacement);
                } else {
                    // Preserve the false match verbatim; don't rescan into it.
                    out.push_str(&text[start..end]);
                }
                cursor = end;
            }
            None => {
                out.push_str(&text[cursor..]);
                break;
            }
        }
    }
    out
}

/// ASCII identifier character predicate. Rego identifiers are
/// `[A-Za-z_][A-Za-z0-9_]*` per grammar, so non-ASCII characters are always
/// boundaries.
const fn is_identifier_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// Derive the outer truthiness condition's `left.provenance` from the
/// last failed helper inner condition. When the outer already has a
/// provenance we don't overwrite; when it has an operand but no provenance,
/// we augment it; when it has no operand at all, we leave it alone (a fully
/// missing `left` on the outer is the engine's signal that the operand isn't
/// meaningfully attributable to a single value).
fn derive_left_provenance_from_helper(
    left: Option<OperandExplanation>,
    helper_conditions: &[ConditionExplanation],
) -> Option<OperandExplanation> {
    let existing = left?;
    if existing.provenance.is_some() {
        return Some(existing);
    }
    // Find the last inner condition whose outcome is "failure" and whose
    // `left` carries a provenance. Iterating in reverse mirrors the fact that
    // a helper body short-circuits on its first failing condition -- the one
    // that actually determined the helper's Undefined/false return.
    let derived_provenance = helper_conditions.iter().rev().find_map(|inner| {
        if inner.outcome != "failure" {
            return None;
        }
        inner.left.as_ref().and_then(|op| op.provenance.clone())
    });
    match derived_provenance {
        Some(prov) => Some(OperandExplanation {
            value: existing.value,
            provenance: Some(prov),
            redacted: existing.redacted,
            source_alias: existing.source_alias,
        }),
        None => Some(existing),
    }
}

fn materialize_condition_window(
    condition_start_index: u32,
    condition_end_index: u32,
    outer_rule_index: u16,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<ConditionExplanation> {
    let relevant_outcomes = select_condition_outcomes_in_window(
        condition_start_index,
        condition_end_index,
        trace,
        settings,
    );

    // Filter out outcomes that belong to a helper rule scope: they are
    // surfaced structurally under `helper_conditions[]` on the outer
    // truthiness record that invoked the helper, so keeping them as siblings
    // here would duplicate them.
    let outer_only: Vec<(usize, &ConditionOutcome)> = relevant_outcomes
        .into_iter()
        .filter(|(_, o)| o.rule_index == outer_rule_index)
        .collect();

    finalize_condition_explanations(
        materialize_condition_explanations(outer_only, program, trace, settings),
        settings,
        true,
    )
}

fn finalize_condition_explanations(
    mut conditions: Vec<ConditionExplanation>,
    settings: &ExplanationSettings,
    dedupe_for_emissions: bool,
) -> Vec<ConditionExplanation> {
    if dedupe_for_emissions && settings.detail != ExplanationDetail::Full {
        conditions = dedupe_emission_conditions(conditions);
    }

    if settings.detail == ExplanationDetail::Compact {
        conditions = compact_condition_explanations(conditions);
    }

    conditions
}

fn compact_condition_explanations(
    conditions: Vec<ConditionExplanation>,
) -> Vec<ConditionExplanation> {
    if conditions.is_empty() {
        return conditions;
    }

    let last_index = conditions.len().saturating_sub(1);

    conditions
        .into_iter()
        .enumerate()
        .filter_map(|(index, mut condition)| {
            let keep = index == last_index
                || condition.outcome != "success"
                || condition.kind == "existence";

            if !keep {
                return None;
            }

            condition.text = compact_condition_text(&condition);
            condition.location = None;
            condition.left = None;
            condition.right = None;
            condition.witness = None;

            Some(condition)
        })
        .collect()
}

fn compact_condition_text(condition: &ConditionExplanation) -> String {
    let Some(witness) = condition.witness.as_ref() else {
        return condition.text.clone();
    };

    alloc::format!(
        "{} [{}]",
        condition.text,
        format_loop_witness_summary(witness)
    )
}

fn format_loop_witness_summary(witness: &LoopWitnessExplanation) -> String {
    let mut summary = alloc::format!(
        "loop: {}/{} matched",
        witness.success_count,
        witness.total_iterations
    );

    if let Some(sample) = format_loop_witness_sample(witness) {
        summary.push_str("; sample: ");
        summary.push_str(&sample);
    }

    summary
}

fn format_loop_witness_sample(witness: &LoopWitnessExplanation) -> Option<String> {
    match (&witness.sample_key, &witness.sample_value) {
        (Some(key), Some(value)) => Some(alloc::format!("{key} => {value}")),
        (Some(key), None) => Some(key.to_string()),
        (None, Some(value)) => Some(value.to_string()),
        (None, None) => None,
    }
}

fn dedupe_emission_conditions(conditions: Vec<ConditionExplanation>) -> Vec<ConditionExplanation> {
    let mut deduped: Vec<ConditionExplanation> = Vec::new();

    'outer: for condition in conditions {
        for existing in &deduped {
            if existing.text == condition.text
                && existing.outcome == condition.outcome
                && existing.kind == condition.kind
                && existing.operator == condition.operator
                && operands_match(existing.left.as_ref(), condition.left.as_ref())
                && operands_match(existing.right.as_ref(), condition.right.as_ref())
                && witnesses_match(existing.witness.as_ref(), condition.witness.as_ref())
            {
                continue 'outer;
            }
        }

        deduped.push(condition);
    }

    deduped
}

fn operands_match(left: Option<&OperandExplanation>, right: Option<&OperandExplanation>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => {
            left.value == right.value
                && left.provenance == right.provenance
                && left.redacted == right.redacted
        }
        _ => false,
    }
}

fn witnesses_match(
    left: Option<&LoopWitnessExplanation>,
    right: Option<&LoopWitnessExplanation>,
) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => {
            left.total_iterations == right.total_iterations
                && left.success_count == right.success_count
                && left.sample_key == right.sample_key
                && left.sample_value == right.sample_value
        }
        _ => false,
    }
}

fn materialize_condition_explanations(
    relevant_outcomes: Vec<(usize, &ConditionOutcome)>,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<ConditionExplanation> {
    materialize_condition_explanations_at_depth(relevant_outcomes, program, trace, settings, 0)
}

/// Recursion-aware variant. Callers that materialize helper inner
/// bodies bump `depth` so we stop at `MAX_HELPER_DEPTH` to avoid unbounded
/// recursion on pathological policies (mutually-recursive helpers).
fn materialize_condition_explanations_at_depth(
    relevant_outcomes: Vec<(usize, &ConditionOutcome)>,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
    depth: usize,
) -> Vec<ConditionExplanation> {
    let mut conditions: Vec<ConditionExplanation> = Vec::new();

    for (outcome_idx, outcome) in &relevant_outcomes {
        let pc_usize: usize = outcome.pc.try_into().unwrap_or(0);

        let static_info = program
            .condition_infos
            .get(pc_usize)
            .and_then(Option::as_ref);

        let base_text = static_info.map(|i| i.text.clone()).unwrap_or_default();

        let kind = static_info
            .map(|i| format_condition_kind(&i.kind))
            .unwrap_or_else(|| "unknown".to_string());

        let operator = static_info
            .and_then(|i| i.operator.as_ref())
            .map(|op| op.to_string());

        let location = get_source_location(pc_usize, program);

        let outcome_str = if outcome.assumed {
            "assumed"
        } else if outcome.passed {
            "success"
        } else {
            "failure"
        };

        let (left, right) = materialize_operands(outcome, static_info, trace, settings);
        let witness = materialize_loop_witness(outcome, trace);
        let binding_name = static_info.and_then(|i| i.binding_name.clone());
        let builtin_name = static_info.and_then(|i| i.builtin_name.clone());
        let negated = static_info.map(|i| i.negated).unwrap_or(false);
        let text = decorate_condition_text(base_text, static_info, left.as_ref());

        // For a truthiness condition whose backing Guard fires on a register
        // written by a rule call (`_helper(x)` or `not _helper(x)`), stitch
        // the helper's evaluated inner conditions as structural children.
        let helper_conditions = materialize_helper_conditions(
            pc_usize,
            *outcome_idx,
            outcome.rule_index,
            program,
            trace,
            settings,
            depth,
        );

        // Derive outer `left.provenance` from the last failed helper inner
        // condition when the outer condition doesn't already carry one.
        let left = derive_left_provenance_from_helper(left, &helper_conditions);

        conditions.push(ConditionExplanation {
            text,
            outcome: outcome_str.to_string(),
            location,
            kind,
            operator,
            left,
            right,
            witness,
            binding_name,
            builtin_name,
            negated,
            helper_conditions,
        });
    }

    if conditions
        .iter()
        .all(|condition| condition.witness.is_none())
    {
        if let Some(witness) = materialize_fallback_loop_witness(&relevant_outcomes, trace) {
            if let Some(last) = conditions.last_mut() {
                last.witness = Some(witness);
            }
        }
    }

    conditions
}

fn materialize_fallback_loop_witness(
    relevant_outcomes: &[(usize, &ConditionOutcome)],
    trace: &EvaluationTrace,
) -> Option<LoopWitnessExplanation> {
    let selected_indices: Vec<u32> = relevant_outcomes
        .iter()
        .filter_map(|(index, _)| u32::try_from(*index).ok())
        .collect();

    let stat = trace
        .loop_stats
        .iter()
        .rev()
        .find(|stat| {
            stat.anchor_condition_idx
                .is_some_and(|idx| selected_indices.contains(&idx))
        })
        .or_else(|| trace.loop_stats.last())?;

    Some(LoopWitnessExplanation {
        total_iterations: stat.total_iterations,
        success_count: stat.success_count,
        sample_key: stat
            .sample_key
            .and_then(|idx| trace.get_value(idx))
            .cloned(),
        sample_value: stat
            .sample_value
            .and_then(|idx| trace.get_value(idx))
            .cloned(),
    })
}

fn materialize_loop_witness(
    outcome: &ConditionOutcome,
    trace: &EvaluationTrace,
) -> Option<LoopWitnessExplanation> {
    let stat = outcome
        .loop_stat_idx
        .and_then(|idx| trace.loop_stats.get(usize::from(idx)))?;

    Some(LoopWitnessExplanation {
        total_iterations: stat.total_iterations,
        success_count: stat.success_count,
        sample_key: stat
            .sample_key
            .and_then(|idx| trace.get_value(idx))
            .cloned(),
        sample_value: stat
            .sample_value
            .and_then(|idx| trace.get_value(idx))
            .cloned(),
    })
}

fn decorate_condition_text(
    base_text: String,
    static_info: Option<&crate::static_provenance::StaticConditionInfo>,
    left: Option<&OperandExplanation>,
) -> String {
    let Some(info) = static_info else {
        return base_text;
    };

    match info.kind {
        crate::static_provenance::ConditionKind::Existence => left
            .map(format_operand_for_text)
            .filter(|value| !value.is_empty())
            .map(|value| alloc::format!("{base_text} [matched: {value}]"))
            .unwrap_or(base_text),
        _ => base_text,
    }
}

fn format_operand_for_text(operand: &OperandExplanation) -> String {
    operand.provenance.as_ref().map_or_else(
        || operand.value.to_string(),
        |path| alloc::format!("{path}={}", operand.value),
    )
}

fn select_condition_outcomes<'a>(
    first_pc: u32,
    last_pc: u32,
    trace: &'a EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<(usize, &'a ConditionOutcome)> {
    let outcomes: Vec<(usize, &ConditionOutcome)> = trace
        .condition_outcomes
        .iter()
        .enumerate()
        .filter(|outcome| outcome.1.pc >= first_pc && outcome.1.pc <= last_pc)
        .collect();

    select_condition_outcomes_from_slice(outcomes, settings)
}

fn select_condition_outcomes_in_window<'a>(
    condition_start_index: u32,
    condition_end_index: u32,
    trace: &'a EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<(usize, &'a ConditionOutcome)> {
    let start_idx = usize::try_from(condition_start_index).unwrap_or(usize::MAX);
    let end_idx = usize::try_from(condition_end_index).unwrap_or(usize::MAX);

    let outcomes: Vec<(usize, &ConditionOutcome)> = trace
        .condition_outcomes
        .get(start_idx..end_idx)
        .unwrap_or(&[])
        .iter()
        .enumerate()
        .map(|(offset, outcome)| (start_idx.saturating_add(offset), outcome))
        .collect();

    select_condition_outcomes_from_slice(outcomes, settings)
}

fn select_condition_outcomes_from_slice<'a>(
    outcomes: Vec<(usize, &'a ConditionOutcome)>,
    settings: &ExplanationSettings,
) -> Vec<(usize, &'a ConditionOutcome)> {
    if settings.condition_mode == ConditionMode::AllContributing {
        return outcomes;
    }

    let mut selected: Vec<(usize, &ConditionOutcome)> = Vec::new();
    let mut seen_pcs: Vec<u32> = Vec::new();

    for outcome in outcomes.iter().rev().copied() {
        if seen_pcs.contains(&outcome.1.pc) {
            continue;
        }
        seen_pcs.push(outcome.1.pc);
        selected.push(outcome);
    }

    selected.reverse();
    selected
}

#[allow(clippy::option_if_let_else)]
fn materialize_operands(
    outcome: &ConditionOutcome,
    static_info: Option<&crate::static_provenance::StaticConditionInfo>,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> (Option<OperandExplanation>, Option<OperandExplanation>) {
    let actual = outcome
        .actual_value_idx
        .and_then(|idx| trace.get_value(idx))
        .cloned();
    let expected = outcome
        .expected_value_idx
        .and_then(|idx| trace.get_value(idx))
        .cloned();

    let (left_prov, right_prov) = static_info
        .and_then(|i| i.operands.as_ref())
        .map(|ops| (ops.left_provenance.as_ref(), ops.right_provenance.as_ref()))
        .unwrap_or((None, None));

    let left_runtime_path = outcome.actual_path.as_deref();
    let right_runtime_path = outcome.expected_path.as_deref();

    let redact = settings.value_mode == ValueMode::Redacted;

    let left_output_path =
        operand_provenance_for_output(left_runtime_path, left_prov, outcome, trace);
    let right_output_path =
        operand_provenance_for_output(right_runtime_path, right_prov, outcome, trace);

    let left = actual.map(|v| {
        let should_redact = redact
            && if left_output_path.is_some() {
                should_redact_runtime_path(left_output_path.as_deref())
            } else {
                should_redact_path(left_prov)
            };
        OperandExplanation {
            value: if should_redact {
                Value::from("<redacted>")
            } else {
                v
            },
            provenance: left_output_path.clone(),
            redacted: should_redact,
            source_alias: left_prov
                .and_then(|p| p.source_alias.as_deref())
                .map(str::to_string),
        }
    });

    let right = expected.map(|v| {
        let should_redact = redact
            && if right_output_path.is_some() {
                should_redact_runtime_path(right_output_path.as_deref())
            } else {
                should_redact_path(right_prov)
            };
        OperandExplanation {
            value: if should_redact {
                Value::from("<redacted>")
            } else {
                v
            },
            provenance: right_output_path.clone(),
            redacted: should_redact,
            source_alias: right_prov
                .and_then(|p| p.source_alias.as_deref())
                .map(str::to_string),
        }
    });

    (left, right)
}

fn materialize_assumptions(program: &Program, trace: &EvaluationTrace) -> Vec<AssumptionRecord> {
    trace
        .assumptions
        .iter()
        .map(|a| {
            let pc_usize: usize = a.pc.try_into().unwrap_or(0);
            let location = get_source_location(pc_usize, program);
            let kind_str = match a.kind {
                AssumptionKind::Exists => "exists",
                AssumptionKind::ConditionHolds => "condition_holds",
                AssumptionKind::CollectionExists => "collection_exists",
                AssumptionKind::NegationHolds => "negation_holds",
            };
            AssumptionRecord {
                kind: kind_str.to_string(),
                input_path: a.input_path.clone(),
                assumed_holds: a.condition_text.clone(),
                operator: a.operator.clone(),
                assumed_value: a.assumed_value.clone(),
                location,
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn get_source_location(pc: usize, program: &Program) -> Option<SourceLocation> {
    let span = program.instruction_spans.get(pc)?.as_ref()?;
    let file_name = program
        .sources
        .get(span.source_index)
        .map(|s| s.name.clone())
        .unwrap_or_default();
    Some(SourceLocation {
        file: file_name,
        row: span.line,
        col: span.column,
    })
}

fn find_rule_return_pc(start_pc: usize, program: &Program) -> u32 {
    let mut pc = start_pc;
    while pc < program.instructions.len() {
        if matches!(
            program.instructions.get(pc),
            Some(crate::rvm::Instruction::RuleReturn {})
        ) {
            return u32::try_from(pc).unwrap_or(u32::MAX);
        }
        pc = pc.saturating_add(1);
    }
    u32::try_from(program.instructions.len().saturating_sub(1)).unwrap_or(u32::MAX)
}

fn format_condition_kind(kind: &crate::static_provenance::ConditionKind) -> String {
    use crate::static_provenance::ConditionKind;
    match *kind {
        ConditionKind::Comparison => "comparison",
        ConditionKind::Membership => "membership",
        ConditionKind::Truthiness => "truthiness",
        ConditionKind::Existence => "existence",
        ConditionKind::EqualityAssertion => "equality_assertion",
        ConditionKind::Binding => "binding",
        ConditionKind::Builtin => "builtin",
    }
    .to_string()
}

#[cfg(all(test, feature = "explanations"))]
#[allow(clippy::indexing_slicing, clippy::unwrap_used)]
mod tests {
    use alloc::vec;
    use alloc::vec::Vec;

    use super::{
        dedupe_emission_conditions, materialize, materialize_condition_explanations,
        materialize_conditions, materialize_rule_emissions, ConditionExplanation,
        OperandExplanation,
    };
    use crate::evaluation_trace::{
        AssumptionKind, ConditionMode, EvaluationTrace, ExplanationDetail, ExplanationScope,
        ExplanationSettings, ValueMode,
    };
    use crate::rvm::program::{Program, RuleInfo, RuleType, SourceFile, SpanInfo};
    use crate::static_provenance::{ConditionKind, StaticConditionInfo};
    use crate::{value::Value, Rc};

    fn settings(condition_mode: ConditionMode) -> ExplanationSettings {
        ExplanationSettings {
            enabled: true,
            value_mode: ValueMode::Redacted,
            condition_mode,
            scope: ExplanationScope::AllEmissions,
            detail: ExplanationDetail::Standard,
            emission_index: None,
            emission_value: None,
            assume_unknown_input: false,
            eval_mode: crate::evaluation_trace::EvaluationMode::Causality,
            unknowns: vec![alloc::string::String::from("input")],
        }
    }

    fn settings_with_detail(
        condition_mode: ConditionMode,
        detail: ExplanationDetail,
    ) -> ExplanationSettings {
        ExplanationSettings {
            detail,
            ..settings(condition_mode)
        }
    }

    #[test]
    fn primary_only_keeps_last_outcome_per_condition_site() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "a\nb\nc\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 1)),
            Some(SpanInfo::new(0, 2, 1, 1)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "cond one".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "cond two".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(1, false, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);

        let conditions = materialize_conditions(
            1,
            2,
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(conditions.len(), 2);
        assert_eq!(
            conditions.first().map(|c| c.text.as_str()),
            Some("cond one")
        );
        assert_eq!(
            conditions.first().map(|c| c.outcome.as_str()),
            Some("failure")
        );
        assert_eq!(conditions.get(1).map(|c| c.text.as_str()), Some("cond two"));
        assert_eq!(
            conditions.get(1).map(|c| c.outcome.as_str()),
            Some("success")
        );
    }

    #[test]
    fn all_contributing_keeps_all_outcomes() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "a\nb\n".into()));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 1))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "cond".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(1, false, false, None, None, None, None, 0);

        let conditions = materialize_conditions(
            1,
            1,
            &program,
            &trace,
            &settings(ConditionMode::AllContributing),
        );

        assert_eq!(conditions.len(), 2);
    }

    #[test]
    fn partial_set_rule_materializes_per_emission_conditions() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "first\nsecond\nsecond\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 6)),
            Some(SpanInfo::new(0, 3, 1, 6)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 0, 3, Value::from("violation a"));
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"));
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"));

        let emissions = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(emissions.len(), 2);
        assert_eq!(emissions[0].index, 0);
        assert_eq!(
            emissions.first().map(|emission| emission.result.clone()),
            Some(Value::from("violation a"))
        );
        assert_eq!(
            emissions.first().map(|emission| emission.conditions.len()),
            Some(2)
        );
        assert_eq!(
            emissions.get(1).map(|emission| emission.result.clone()),
            Some(Value::from("violation b"))
        );
        assert_eq!(emissions[1].index, 1);
        assert_eq!(
            emissions.get(1).map(|emission| emission.conditions.len()),
            Some(2)
        );
    }

    #[test]
    fn partial_set_rule_can_select_single_emission_by_index() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "first\nsecond\nsecond\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 6)),
            Some(SpanInfo::new(0, 3, 1, 6)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 0, 3, Value::from("violation a"));
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"));

        let emissions = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &ExplanationSettings {
                emission_index: Some(1),
                scope: ExplanationScope::SingleEmission,
                ..settings(ConditionMode::PrimaryOnly)
            },
        );

        assert_eq!(emissions.len(), 1);
        assert_eq!(emissions[0].index, 1);
        assert_eq!(emissions[0].result, Value::from("violation b"));
        assert_eq!(emissions[0].conditions.len(), 2);
    }

    #[test]
    fn partial_set_rule_can_select_single_emission_by_value() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "first\nsecond\nsecond\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 6)),
            Some(SpanInfo::new(0, 3, 1, 6)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 0, 3, Value::from("violation a"));
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"));

        let emissions = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &ExplanationSettings {
                scope: ExplanationScope::SingleEmission,
                emission_value: Some(Value::from("violation a")),
                ..settings(ConditionMode::PrimaryOnly)
            },
        );

        assert_eq!(emissions.len(), 1);
        assert_eq!(emissions[0].index, 0);
        assert_eq!(emissions[0].result, Value::from("violation a"));
        assert_eq!(emissions[0].conditions.len(), 2);
    }

    #[test]
    fn standard_detail_dedupes_emission_conditions_but_full_keeps_all() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "dup\ndup\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 3)),
            Some(SpanInfo::new(0, 2, 1, 3)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "dup".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "dup".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 0, 2, Value::from("violation a"));

        let standard = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::AllContributing, ExplanationDetail::Standard),
        );
        let full = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::AllContributing, ExplanationDetail::Full),
        );

        assert_eq!(standard.len(), 1);
        assert_eq!(standard[0].conditions.len(), 1);
        assert_eq!(full.len(), 1);
        assert_eq!(full[0].conditions.len(), 2);
    }

    #[test]
    fn compact_detail_inlines_witness_and_last_condition_but_strips_operands() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "helper\nsome item in coll\nfinal\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 6)),
            Some(SpanInfo::new(0, 2, 1, 17)),
            Some(SpanInfo::new(0, 3, 1, 5)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "helper".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "some item in coll".into(),
                kind: ConditionKind::Existence,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "final".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(
            2,
            true,
            false,
            Some(Value::from("match-a")),
            None,
            None,
            None,
            0,
        );
        trace.attach_loop_stat_to_last_condition(
            2,
            3,
            2,
            Some(Value::from(1_u64)),
            Some(Value::from("match-a")),
        );
        trace.record_condition(3, true, false, None, None, None, None, 0);

        let conditions = materialize_conditions(
            1,
            3,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::AllContributing, ExplanationDetail::Compact),
        );

        assert_eq!(conditions.len(), 2);
        assert_eq!(
            conditions[0].text,
            "some item in coll [matched: \"match-a\"] [loop: 2/3 matched; sample: 1 => \"match-a\"]"
        );
        assert_eq!(conditions[0].kind, "existence");
        assert!(conditions[0].left.is_none());
        assert!(conditions[0].right.is_none());
        assert!(conditions[0].location.is_none());
        assert!(conditions[0].witness.is_none());
        assert_eq!(conditions[1].text, "final");
        assert!(conditions[1].left.is_none());
        assert!(conditions[1].location.is_none());
    }

    #[test]
    fn standard_detail_keeps_structured_loop_witness() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "every item in input.list { item > 0 }\n".into(),
        ));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 34))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "every item in input.list { item > 0 }".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, Some(Value::Bool(true)), None, None, None, 0);
        trace.attach_loop_stat_to_last_condition(
            1,
            3,
            2,
            Some(Value::from(1_u64)),
            Some(Value::from("match-a")),
        );

        let conditions = materialize_conditions(
            1,
            1,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::PrimaryOnly, ExplanationDetail::Standard),
        );

        assert_eq!(conditions.len(), 1);
        assert_eq!(conditions[0].text, "every item in input.list { item > 0 }");
        let witness = conditions[0].witness.as_ref().unwrap();
        assert_eq!(witness.total_iterations, 3);
        assert_eq!(witness.success_count, 2);
        assert_eq!(witness.sample_key, Some(Value::from(1_u64)));
        assert_eq!(witness.sample_value, Some(Value::from("match-a")));
    }

    #[test]
    fn compact_detail_suppresses_partial_set_definition_scaffolding_and_assumptions() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "first\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 1, 1, 5)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            None,
        ];
        program.instructions = vec![
            crate::rvm::Instruction::LoadTrue { dest: 0 },
            crate::rvm::Instruction::LoadTrue { dest: 0 },
            crate::rvm::Instruction::RuleReturn {},
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info);

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_rule_outcome(0, 0, true, Some(Value::from("violation a")));
        trace.record_emission(0, 0, 0, 1, Value::from("violation a"));
        trace.record_assumption(
            AssumptionKind::ConditionHolds,
            "input.foo".into(),
            "input.foo == true".into(),
            1,
            Some("==".into()),
            Some(Value::Bool(true)),
            0,
            0,
            None,
            0,
            Vec::new(),
        );

        let report = materialize(
            &program,
            &trace,
            &settings_with_detail(ConditionMode::PrimaryOnly, ExplanationDetail::Compact),
            Value::from("violation a"),
        );

        assert_eq!(report.assumptions.len(), 0);
        assert_eq!(report.rules.len(), 1);
        assert_eq!(report.rules[0].emissions.len(), 1);
        assert_eq!(report.rules[0].definitions.len(), 0);
    }

    #[test]
    fn quantifier_condition_materializes_loop_witness_summary() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "every item in input.list { item > 0 }\n".into(),
        ));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 34))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "every item in input.list { item > 0 }".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, Some(Value::Bool(true)), None, None, None, 0);
        trace.attach_loop_stat_to_last_condition(
            1,
            3,
            2,
            Some(Value::from(1_u64)),
            Some(Value::from("match-a")),
        );

        let conditions = materialize_conditions(
            1,
            1,
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(conditions.len(), 1);
        let witness = conditions[0].witness.as_ref().unwrap();
        assert_eq!(witness.total_iterations, 3);
        assert_eq!(witness.success_count, 2);
        assert_eq!(witness.sample_key, Some(Value::from(1_u64)));
        assert_eq!(witness.sample_value, Some(Value::from("match-a")));
    }

    #[test]
    fn fallback_loop_witness_attaches_to_last_selected_condition() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "n > 1\nn < 3\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 5)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "n > 1".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "n < 3".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, Some(Value::Bool(true)), None, None, None, 0);
        trace.record_condition(
            2,
            false,
            false,
            Some(Value::Bool(false)),
            None,
            None,
            None,
            0,
        );
        trace.record_loop(
            2,
            Some(1),
            3,
            1,
            Some(Value::from(1_u64)),
            Some(Value::from(2_u64)),
        );

        let conditions = materialize_conditions(
            1,
            2,
            &program,
            &trace,
            &settings(ConditionMode::AllContributing),
        );

        assert_eq!(conditions.len(), 2);
        assert!(conditions[0].witness.is_none());
        let witness = conditions[1].witness.as_ref().unwrap();
        assert_eq!(witness.total_iterations, 3);
        assert_eq!(witness.success_count, 1);
        assert_eq!(witness.sample_key, Some(Value::from(1_u64)));
        assert_eq!(witness.sample_value, Some(Value::from(2_u64)));
    }

    #[test]
    fn rule_summary_scope_suppresses_definitions_and_emissions() {
        let mut program = Program::new();
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info);

        let mut trace = EvaluationTrace::new();
        trace.record_rule_outcome(0, 0, true, Some(Value::from("violation a")));
        trace.record_emission(0, 0, 0, 0, Value::from("violation a"));

        let report = materialize(
            &program,
            &trace,
            &ExplanationSettings {
                scope: ExplanationScope::RuleSummary,
                ..settings_with_detail(ConditionMode::PrimaryOnly, ExplanationDetail::Standard)
            },
            Value::from("violation a"),
        );

        assert_eq!(report.rules.len(), 1);
        assert_eq!(report.rules[0].emissions.len(), 0);
        assert_eq!(report.rules[0].definitions.len(), 0);
    }

    #[test]
    fn existence_condition_text_includes_matched_value() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "some item in coll\n".into(),
        ));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 8))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "some item in coll".into(),
                kind: ConditionKind::Existence,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(
            1,
            true,
            false,
            Some(Value::from("match-a")),
            None,
            None,
            None,
            0,
        );

        let conditions = materialize_condition_explanations(
            trace.condition_outcomes.iter().enumerate().collect(),
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(
            conditions.first().map(|condition| condition.text.as_str()),
            Some("some item in coll [matched: \"match-a\"]")
        );
    }

    #[test]
    fn emission_dedup_keeps_distinct_witness_values() {
        let conditions = vec![
            ConditionExplanation {
                text: "some item in coll [matched: a]".into(),
                outcome: "success".into(),
                location: None,
                kind: "existence".into(),
                operator: None,
                left: Some(OperandExplanation {
                    value: Value::from("a"),
                    provenance: None,
                    redacted: false,
                    source_alias: None,
                }),
                right: None,
                witness: None,
                binding_name: None,
                builtin_name: None,
                negated: false,
                helper_conditions: Vec::new(),
            },
            ConditionExplanation {
                text: "some item in coll [matched: b]".into(),
                outcome: "success".into(),
                location: None,
                kind: "existence".into(),
                operator: None,
                left: Some(OperandExplanation {
                    value: Value::from("b"),
                    provenance: None,
                    redacted: false,
                    source_alias: None,
                }),
                right: None,
                witness: None,
                binding_name: None,
                builtin_name: None,
                negated: false,
                helper_conditions: Vec::new(),
            },
        ];

        let deduped = dedupe_emission_conditions(conditions);

        assert_eq!(deduped.len(), 2);
    }
}
