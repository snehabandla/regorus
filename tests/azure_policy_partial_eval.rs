// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(all(feature = "azure_policy", feature = "explanations", feature = "rvm"))]

//! Partial evaluation and causality for Azure-Policy-compiled programs.
//!
//! These tests pin concrete evaluation, residual identity and boolean shape,
//! definitiveness, pruning, declared-unknown scoping, and context provenance.
//!
//! Two facts about the AP path drive the harness shape, and both contradict
//! assumptions recorded in the plan before this step ran:
//!
//! 1. `resourceGroup()` compiles to `LoadContext`, which reads the VM's
//!    dedicated context slot (`RegoVM::set_context`). It is **not** read from
//!    `input.context`, so the "input envelope" shape does not reach it.
//! 2. `LoadContext` sets no provenance root (unlike `LoadInput`/`LoadData`), so
//!    no context-derived register can ever match a declared unknown path.
//!
//! Known limitation: `field:` conditions whose missing operands are coalesced
//! to null do not currently residualize. A dedicated test below pins that
//! boundary separately from the supported `value:` condition path.

use regorus::evaluation_trace::{
    ConditionMode, EvaluationMode, ExplanationDetail, ExplanationScope, ExplanationSettings,
    ValueMode,
};
use regorus::languages::azure_policy::{compiler, parser};
use regorus::rvm::RegoVM;
use regorus::{Source, Value};

/// The plan's gated policy, with one deliberate substitution.
///
/// The third condition uses a plain property path rather than the
/// fully-qualified `Microsoft.Storage/storageAccounts/allowSharedKeyAccess`
/// alias: with no alias registry loaded, an alias resolves to itself and would
/// compile to a single `/`-containing key rather than a property path. The
/// semantics under test (`notEquals false` against an absent field) are
/// identical either way.
const GATED_POLICY: &str = r#"{
  "displayName": "Prod storage must not disable shared key access",
  "policyRule": {
    "if": {
      "allOf": [
        { "field": "type", "equals": "Microsoft.Storage/storageAccounts" },
        { "value": "[resourceGroup().name]", "equals": "prod-rg" },
        { "field": "properties.allowSharedKeyAccess", "notEquals": false }
      ]
    },
    "then": { "effect": "deny" }
  }
}"#;

/// `allOf` where a concrete-false sibling follows the unknown-dependent one.
const PRUNING_POLICY: &str = r#"{
  "displayName": "Prod storage in westus",
  "policyRule": {
    "if": {
      "allOf": [
        { "value": "[resourceGroup().name]", "equals": "prod-rg" },
        { "field": "location", "equals": "westus" }
      ]
    },
    "then": { "effect": "deny" }
  }
}"#;

/// `anyOf` where a concrete-true alternative accompanies the unknown-dependent one.
const DISJUNCTION_POLICY: &str = r#"{
  "displayName": "Prod storage or eastus",
  "policyRule": {
    "if": {
      "anyOf": [
        { "value": "[resourceGroup().name]", "equals": "prod-rg" },
        { "field": "location", "equals": "eastus" }
      ]
    },
    "then": { "effect": "deny" }
  }
}"#;

/// `anyOf` where *both* alternatives depend on unknown deployment context, so a
/// correct residual is a genuine disjunction rather than one conjunction.
const TWO_UNKNOWN_ALTERNATIVES_POLICY: &str = r#"{
  "displayName": "Prod resource group or eastus deployment",
  "policyRule": {
    "if": {
      "anyOf": [
        { "value": "[resourceGroup().name]", "equals": "prod-rg" },
        { "value": "[resourceGroup().location]", "equals": "eastus" }
      ]
    },
    "then": { "effect": "deny" }
  }
}"#;

/// `anyOf` where an unknown-dependent alternative accompanies a concretely-false
/// one, so the assumption is the only way the effect can fire.
const SURVIVING_ALTERNATIVE_POLICY: &str = r#"{
  "displayName": "Prod resource group or westus resource",
  "policyRule": {
    "if": {
      "anyOf": [
        { "value": "[resourceGroup().name]", "equals": "prod-rg" },
        { "field": "location", "equals": "westus" }
      ]
    },
    "then": { "effect": "deny" }
  }
}"#;

/// A storage account with `allowSharedKeyAccess` genuinely absent.
///
/// Keys are lowercase because the compiler lowercases every field path segment
/// before emitting the chained index.
const RESOURCE_NO_SHARED_KEY_FIELD: &str = r#"{
  "type": "Microsoft.Storage/storageAccounts",
  "name": "sa1",
  "location": "eastus",
  "properties": {}
}"#;

/// Compile `policy` and build a VM with the input envelope and context set.
///
/// `context` is passed through `set_context` (see module docs). Passing `None`
/// leaves the context empty, which is how a genuinely-unknown deployment target
/// is expressed today.
fn build_vm(policy: &str, resource_json: &str, context_json: Option<&str>) -> RegoVM {
    let source = Source::from_contents("policy.json".to_string(), policy.to_string()).unwrap();
    let defn = parser::parse_policy_definition(&source).expect("policy should parse");
    let program = compiler::compile_policy_definition(&defn).expect("policy should compile");

    let mut input = Value::new_object();
    {
        let map = input.as_object_mut().unwrap();
        map.insert(
            Value::from("resource"),
            Value::from_json_str(resource_json).unwrap(),
        );
        map.insert(Value::from("parameters"), Value::new_object());
    }

    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_input(input);
    vm.set_context(match context_json {
        Some(j) => Value::from_json_str(j).unwrap(),
        None => Value::new_object(),
    });
    vm
}

fn settings(eval_mode: EvaluationMode, unknowns: Vec<String>) -> ExplanationSettings {
    ExplanationSettings {
        enabled: true,
        value_mode: ValueMode::Full,
        condition_mode: ConditionMode::AllContributing,
        scope: ExplanationScope::AllEmissions,
        detail: ExplanationDetail::Full,
        emission_index: None,
        emission_value: None,
        assume_unknown_input: true,
        eval_mode,
        unknowns,
        max_derivations: 1,
    }
}

/// Run `policy` in PE mode and return the parsed PE result.
fn run_ap_pe(
    policy: &str,
    resource_json: &str,
    context_json: Option<&str>,
    unknowns: Vec<String>,
) -> serde_json::Value {
    let mut vm = build_vm(policy, resource_json, context_json);
    vm.set_explanation_settings(settings(EvaluationMode::PartialEval, unknowns));

    let result = vm.execute_entry_point_by_name("main").unwrap();
    let pe = vm.take_partial_eval_result(result).unwrap();
    serde_json::from_str(&pe).unwrap()
}

/// Run `policy` in causality mode and return the parsed causality report.
///
/// Causality is the only output that exposes operand provenance directly, so it
/// is the seam that isolates 15a from the PE machinery of 15b.
fn run_ap_causality(
    policy: &str,
    resource_json: &str,
    context_json: Option<&str>,
) -> serde_json::Value {
    run_ap_causality_with_unknowns(policy, resource_json, context_json, vec!["input".into()])
}

/// Causality mode with declared unknowns, i.e. the second pass a consumer runs
/// alongside partial evaluation to explain an *assumed* violation.
fn run_ap_causality_with_unknowns(
    policy: &str,
    resource_json: &str,
    context_json: Option<&str>,
    unknowns: Vec<String>,
) -> serde_json::Value {
    let mut vm = build_vm(policy, resource_json, context_json);
    vm.set_explanation_settings(settings(EvaluationMode::Causality, unknowns));

    let result = vm.execute_entry_point_by_name("main").unwrap();
    let report = vm.take_causality_report(result).unwrap();
    serde_json::from_str(&report).unwrap()
}

/// Every path a fixed `LoadContext` might plausibly render, so a red result
/// cannot be blamed on having guessed the wrong prefix string.
fn context_unknowns() -> Vec<String> {
    vec![
        "context".into(),
        "input.context".into(),
        "context.resourceGroup".into(),
        "input.context.resourceGroup.name".into(),
    ]
}

fn residuals(pe: &serde_json::Value) -> &Vec<serde_json::Value> {
    pe["residual_queries"]
        .as_array()
        .expect("residual_queries array")
}

const PROD_CONTEXT: &str = r#"{"resourceGroup": {"name": "prod-rg"}}"#;
const DEV_CONTEXT: &str = r#"{"resourceGroup": {"name": "dev-rg"}}"#;

// ---------------------------------------------------------------------------
// Control 1 — concrete matching context
// ---------------------------------------------------------------------------

#[test]
fn control_1_concrete_prod_context_denies_with_no_residual() {
    let pe = run_ap_pe(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        Some(PROD_CONTEXT),
        context_unknowns(),
    );

    assert_eq!(
        pe["result"]["effect"], "deny",
        "a fully concrete matching target must still deny in PE mode, got: {pe}"
    );
    assert!(
        residuals(&pe).is_empty(),
        "a concrete match must not produce residuals, got: {pe}"
    );
}

// ---------------------------------------------------------------------------
// Control 2 — concrete non-matching context
// ---------------------------------------------------------------------------

#[test]
fn control_2_concrete_dev_context_is_undefined_with_no_residual() {
    let pe = run_ap_pe(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        Some(DEV_CONTEXT),
        context_unknowns(),
    );

    assert_eq!(
        pe["result"],
        serde_json::Value::Null,
        "a concrete non-matching target must be undefined (null), got: {pe}"
    );
    assert!(
        residuals(&pe).is_empty(),
        "a concrete non-match must not produce residuals, got: {pe}"
    );
}

// ---------------------------------------------------------------------------
// Control 3 — declared-unknown context: the point of Track E
// ---------------------------------------------------------------------------

#[test]
fn control_3_unknown_context_yields_one_prod_rg_residual() {
    let pe = run_ap_pe(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        None,
        context_unknowns(),
    );

    assert_eq!(
        pe["result"]["effect"], "deny",
        "the effect must stay reachable under the assumption, got: {pe}"
    );

    let queries = residuals(&pe);
    assert_eq!(
        queries.len(),
        1,
        "one unknown condition should yield exactly one disjunct, got: {pe}"
    );

    let conds = queries[0].as_array().expect("conjunction array");
    assert_eq!(
        conds.len(),
        1,
        "only the resource-group condition is unknown, got: {pe}"
    );

    // Dual emission: the normalized symbol drives the shared renderer, the
    // authored name preserves Azure Policy fidelity.
    assert_eq!(conds[0]["operator"], "==", "got: {pe}");
    assert_eq!(conds[0]["builtin_name"], "equals", "got: {pe}");
    assert_eq!(conds[0]["value"], "prod-rg", "got: {pe}");
    assert_eq!(
        conds[0]["input_path"], "context.resourceGroup.name",
        "the residual must name the unknown path, got: {pe}"
    );
    assert_eq!(
        conds[0]["condition"], "",
        "AP must not emit a raw JSON source line consumers would render verbatim, got: {pe}"
    );
}

// ---------------------------------------------------------------------------
// 15d — residual source identity for a rule-less program
// ---------------------------------------------------------------------------

/// A rule-less AP program has no `RuleInfo`, so PE's `source_attribution` used
/// to emit no `source_rule` at all. Bicep joins a residual to its causality
/// violation primarily by rule name, so an absent name forces the residual onto
/// every violation as an unprovenanced tail.
#[test]
fn residual_carries_the_policy_display_name_and_json_row() {
    let pe = run_ap_pe(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        None,
        context_unknowns(),
    );

    let cond = &residuals(&pe)[0][0];
    assert_eq!(
        cond["source_rule"], "Prod storage must not disable shared key access",
        "the residual must name the policy, got: {pe}"
    );
    assert_eq!(cond["source_file"], "policy.json", "got: {pe}");
    assert_eq!(
        cond["source_row"], 7,
        "row should point at the unknown condition's line in the policy JSON, got: {pe}"
    );
}

/// The join key must be *identical* on both sides, not merely present. Causality
/// names its synthetic rule from the same metadata; if the two ever diverge,
/// Bicep's name-primary match silently degrades to the unprovenanced tail.
#[test]
fn residual_source_rule_matches_the_causality_rule_name() {
    let pe = run_ap_pe(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        None,
        context_unknowns(),
    );
    let report = run_ap_causality(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        Some(PROD_CONTEXT),
    );

    assert_eq!(
        residuals(&pe)[0][0]["source_rule"],
        report["rules"][0]["name"],
        "PE and causality must agree on the rule name, got PE: {pe}\ncausality: {report}"
    );
}

// ---------------------------------------------------------------------------
// 15d — does AP need its own definitiveness signal?
// ---------------------------------------------------------------------------

/// `trace.definitive_result` is set only inside `CallRule` handling, so it is
/// permanently false for a rule-less AP program and `materialize_pe`'s early
/// return is dead code here.
///
/// This pins the claim that the flag is nonetheless *unnecessary* for AP: the
/// observable contract is "no residual means the verdict is unconditional", and
/// 15c's orphaning already delivers that. If a case is ever found where AP needs
/// to report definitiveness while live assumptions remain, this test is where it
/// would surface.
#[test]
fn absence_of_residuals_is_the_definitiveness_signal() {
    let concrete = run_ap_pe(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        Some(PROD_CONTEXT),
        context_unknowns(),
    );
    let assumed = run_ap_pe(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        None,
        context_unknowns(),
    );

    // Identical effect, so `result` alone cannot distinguish the two.
    assert_eq!(concrete["result"]["effect"], "deny", "got: {concrete}");
    assert_eq!(assumed["result"]["effect"], "deny", "got: {assumed}");

    assert!(
        residuals(&concrete).is_empty(),
        "an unconditional deny must carry no residual, got: {concrete}"
    );
    assert_eq!(
        residuals(&assumed).len(),
        1,
        "a conditional deny must carry its condition, got: {assumed}"
    );
}

// ---------------------------------------------------------------------------
// Control 4 — missing context that was NOT declared unknown
// ---------------------------------------------------------------------------

/// The discriminator between an assumption and a concrete verdict must be
/// *declared unknown provenance*, not `Undefined` alone. Only `unknowns`
/// differs from control 3, so any divergence is attributable to that alone.
#[test]
fn control_4_undeclared_missing_context_keeps_concrete_semantics() {
    let pe = run_ap_pe(GATED_POLICY, RESOURCE_NO_SHARED_KEY_FIELD, None, Vec::new());

    assert_eq!(
        pe["result"],
        serde_json::Value::Null,
        "an undeclared missing context must fall through to concrete AP semantics, got: {pe}"
    );
    assert!(
        residuals(&pe).is_empty(),
        "an undeclared missing value must never become a residual, got: {pe}"
    );
}

// ---------------------------------------------------------------------------
// Control 5 — a genuinely absent resource field must stay concrete
// ---------------------------------------------------------------------------

/// `notEquals false` against an absent `allowSharedKeyAccess` matches under
/// Azure Policy semantics — this is the SFI shared-key behaviour. Declaring the
/// resource-group path unknown must not drag this unrelated absent field into
/// the assumption set.
#[test]
fn control_5_absent_resource_field_is_not_mislabelled_as_an_assumption() {
    let pe = run_ap_pe(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        Some(PROD_CONTEXT),
        context_unknowns(),
    );

    assert_eq!(
        pe["result"]["effect"], "deny",
        "absent allowSharedKeyAccess must still satisfy `notEquals false`, got: {pe}"
    );

    let mentions_shared_key = residuals(&pe).iter().any(|q| {
        q.as_array().is_some_and(|conds| {
            conds.iter().any(|c| {
                serde_json::to_string(c)
                    .unwrap_or_default()
                    .to_ascii_lowercase()
                    .contains("allowsharedkeyaccess")
            })
        })
    });
    assert!(
        !mentions_shared_key,
        "a genuinely absent field must never appear as an assumption, got: {pe}"
    );
}

/// Probes whether the 15b branch reaches `field:` conditions at all.
///
/// The resource-field path is *declared unknown* here, so a `value:`-style
/// condition would residualize. It does not, because `compile_condition`
/// coalesces an undefined `field:` operand to `Null` before the comparison, so
/// the operand the PE branch inspects is never `Value::Undefined`.
///
/// Recorded rather than fixed: Bicep's deployment targets map to *context*
/// (`value:` conditions), so 15b covers the Step 16 path. Declaring a resource
/// field unknown is a Step 16b question, not a 15b regression.
#[test]
fn field_conditions_do_not_residualize_because_operands_are_coalesced_to_null() {
    let pe = run_ap_pe(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        Some(PROD_CONTEXT),
        vec!["input.resource.properties.allowsharedkeyaccess".into()],
    );

    assert_eq!(
        pe["result"]["effect"], "deny",
        "concrete AP semantics still apply, got: {pe}"
    );
    assert!(
        residuals(&pe).is_empty(),
        "a declared-unknown `field:` operand does not reach the PE branch today, got: {pe}"
    );
}

// ---------------------------------------------------------------------------
// Control 6 — a concrete false sibling prunes an earlier assumption
// ---------------------------------------------------------------------------

/// No longer vacuous after 15b: an assumption *is* now recorded, and 15c must
/// prune it. Rego marks assumptions `orphaned` at definition end in `rules.rs`,
/// which a rule-less AP program never reaches; the AP equivalent is the
/// logical-block frame closed by `AllOfNext` / `LogicalBlockEnd`.
#[test]
fn control_6_concrete_false_sibling_leaves_no_orphan_residual() {
    // Resource location is eastus; the policy requires westus, so the second
    // `allOf` child is concretely false regardless of the resource group.
    let pe = run_ap_pe(
        PRUNING_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        None,
        context_unknowns(),
    );

    assert_eq!(
        pe["result"],
        serde_json::Value::Null,
        "a concretely-false conjunct makes the whole allOf false, got: {pe}"
    );
    assert!(
        residuals(&pe).is_empty(),
        "no residual may survive a concretely-false sibling, got: {pe}"
    );
}

// ---------------------------------------------------------------------------
// Control 7 — a concrete true alternative makes an anyOf definitive
// ---------------------------------------------------------------------------

/// Soundness, not just tidiness: before 15c an assumed-true alternative
/// short-circuited the `anyOf`, so the concretely-true alternative never ran and
/// the residual claimed a condition the effect did not actually depend on.
#[test]
fn control_7_concrete_true_alternative_makes_anyof_definitive() {
    // Resource location is eastus, satisfying the second `anyOf` alternative
    // outright, so the unknown resource-group alternative is irrelevant.
    let pe = run_ap_pe(
        DISJUNCTION_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        None,
        context_unknowns(),
    );

    assert_eq!(
        pe["result"]["effect"], "deny",
        "a concretely-true alternative must decide the anyOf, got: {pe}"
    );
    assert!(
        residuals(&pe).is_empty(),
        "a definitive result must drop irrelevant unknown alternatives, got: {pe}"
    );
}

// ---------------------------------------------------------------------------
// anyOf with two unknown alternatives — the DNF shape
// ---------------------------------------------------------------------------

/// `materialize_pe` groups conjuncts by `(conjunction_id, iteration_index)`.
/// Without per-alternative conjunction scoping, both alternatives land in
/// conjunction 0 and materialize as a single AND-clause — a residual claiming
/// *both* must hold, when the policy requires only one.
#[test]
fn anyof_with_two_unknown_alternatives_yields_two_disjuncts() {
    let pe = run_ap_pe(
        TWO_UNKNOWN_ALTERNATIVES_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        None,
        context_unknowns(),
    );

    assert_eq!(
        pe["result"]["effect"], "deny",
        "the effect stays reachable under either assumption, got: {pe}"
    );

    let queries = residuals(&pe);
    assert_eq!(
        queries.len(),
        2,
        "each unknown alternative must be its own disjunct (OR), got: {pe}"
    );
    for disjunct in queries {
        let conds = disjunct.as_array().expect("conjunction array");
        assert_eq!(
            conds.len(),
            1,
            "alternatives must not be AND-ed together, got: {pe}"
        );
    }

    let paths: Vec<&str> = queries
        .iter()
        .filter_map(|d| d[0]["input_path"].as_str())
        .collect();
    assert!(
        paths.contains(&"context.resourceGroup.name")
            && paths.contains(&"context.resourceGroup.location"),
        "both alternatives must be represented, got: {pe}"
    );
}

/// The mirror of control 7, and the case control 7 alone cannot pin.
///
/// Control 7 stays green under a wrong variant that short-circuits on an
/// assumed-true child *and* discards its assumptions, because there the effect
/// really is unconditional. Here no other alternative can fire, so discarding
/// the assumption would silently turn a conditional deny into an unconditional
/// one.
#[test]
fn anyof_keeps_the_assumption_when_no_other_alternative_can_fire() {
    // Resource location is eastus; the policy's concrete alternative wants
    // westus, so only the unknown resource-group alternative can hold.
    let pe = run_ap_pe(
        SURVIVING_ALTERNATIVE_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        None,
        context_unknowns(),
    );

    assert_eq!(
        pe["result"]["effect"], "deny",
        "the effect must remain reachable under the assumption, got: {pe}"
    );

    let queries = residuals(&pe);
    assert_eq!(
        queries.len(),
        1,
        "exactly one surviving disjunct, got: {pe}"
    );
    let conds = queries[0].as_array().expect("conjunction array");
    assert_eq!(conds.len(), 1, "got: {pe}");
    assert_eq!(
        conds[0]["input_path"], "context.resourceGroup.name",
        "got: {pe}"
    );
    assert_eq!(conds[0]["value"], "prod-rg", "got: {pe}");
}

// ---------------------------------------------------------------------------
// 15f — causality must follow the same branch partial evaluation took
// ---------------------------------------------------------------------------

/// A consumer that reports an *assumed* violation needs two passes: PE for the
/// residual, causality for the property the author can actually change. Both
/// must describe the same branch.
///
/// Before 15f, `maybe_assume_policy_condition` required `PartialEval`, so the
/// causality pass took the *concrete* branch instead: the gate evaluated false,
/// no effect was emitted, and the report explained why the policy did **not**
/// match. A consumer pairing that with a PE "would deny" verdict rendered an
/// inverted, plausible-looking explanation — worse than none.
#[test]
fn causality_with_declared_unknowns_follows_the_assumed_branch() {
    let report = run_ap_causality_with_unknowns(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        None,
        context_unknowns(),
    );

    assert_eq!(
        report["query_result"]["effect"], "deny",
        "the effect must be reached under the assumption, got: {report}"
    );

    let conditions = report["rules"][0]["definitions"][0]["conditions"]
        .as_array()
        .expect("conditions array");

    // The assumed gate is recorded as an assumption, not as a cause, so the
    // reported conditions are the ones the author can act on.
    assert!(
        conditions
            .iter()
            .any(|c| c["left"]["provenance"] == "input.resource.properties.allowsharedkeyaccess"),
        "the actionable resource condition must be explained, got: {report}"
    );
    assert!(
        !conditions
            .iter()
            .any(|c| c["left"]["provenance"] == "context.resourceGroup.name"),
        "the assumed gate must not be reported as a cause, got: {report}"
    );
}

/// Negative control: without declared unknowns the concrete branch still wins,
/// so this change cannot silently alter ordinary Azure Policy causality.
#[test]
fn causality_without_declared_unknowns_keeps_concrete_semantics() {
    let report = run_ap_causality(GATED_POLICY, RESOURCE_NO_SHARED_KEY_FIELD, None);

    assert_eq!(
        report["query_result"], "<undefined>",
        "an undeclared missing context still fails the gate, got: {report}"
    );
}

// ---------------------------------------------------------------------------
// 15a — context-derived registers carry provenance
// ---------------------------------------------------------------------------

/// Isolates 15a from 15b by observing provenance directly.
///
/// A residual cannot serve as 15a's acceptance: it additionally requires
/// `PolicyCondition` to record a PE assumption, which is 15b. The causality
/// report exposes operand provenance unfiltered, so it observes the provenance
/// root alone.
///
/// The path is rooted at `context`, not `input.context`: `LoadContext` reads a
/// dedicated VM slot that no input envelope feeds.
#[test]
fn step_15a_context_derived_register_carries_provenance() {
    let report = run_ap_causality(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        Some(PROD_CONTEXT),
    );

    let conditions = report["rules"][0]["definitions"][0]["conditions"]
        .as_array()
        .expect("conditions array");

    let rg_condition = conditions
        .iter()
        .find(|c| c["right"]["value"] == "prod-rg")
        .unwrap_or_else(|| panic!("resource-group condition should be reported, got: {report}"));

    assert_eq!(
        rg_condition["left"]["provenance"], "context.resourceGroup.name",
        "resourceGroup().name must carry a context-rooted path, got: {report}"
    );
}

/// Negative control for the test above: a resource-derived operand in the same
/// report stays rooted at `input`, so a passing provenance assertion cannot be
/// explained by the tracker having been made unconditionally permissive.
#[test]
fn step_15a_resource_provenance_root_is_unchanged() {
    let report = run_ap_causality(
        GATED_POLICY,
        RESOURCE_NO_SHARED_KEY_FIELD,
        Some(PROD_CONTEXT),
    );

    let conditions = report["rules"][0]["definitions"][0]["conditions"]
        .as_array()
        .expect("conditions array");

    let type_condition = conditions
        .iter()
        .find(|c| c["right"]["value"] == "Microsoft.Storage/storageAccounts")
        .unwrap_or_else(|| panic!("type condition should be reported, got: {report}"));

    assert_eq!(
        type_condition["left"]["provenance"], "input.resource.type",
        "resource fields must stay rooted at input, got: {report}"
    );
}
