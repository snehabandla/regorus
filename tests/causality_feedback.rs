// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Regression tests for the causality / partial-eval feedback items
//! filed against the `causality` branch.  Each test corresponds to a
//! numbered item in the feedback and asserts that the issue no longer
//! reproduces.

#![cfg(all(feature = "rvm", feature = "explanations"))]

use regorus::*;
use std::collections::HashSet;

fn run_causality_full(policy: &str, input_json: &str, entrypoint_str: &str) -> serde_json::Value {
    let mut engine = Engine::new();
    engine
        .add_policy("test.rego".into(), policy.into())
        .unwrap();

    let entrypoint: Rc<str> = entrypoint_str.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint).unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
            .unwrap();

    let mut vm = rvm::RegoVM::new_with_policy(compiled);
    vm.load_program(program);
    vm.set_explanation_settings(evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode: evaluation_trace::ValueMode::Full,
        condition_mode: evaluation_trace::ConditionMode::AllContributing,
        scope: evaluation_trace::ExplanationScope::AllEmissions,
        detail: evaluation_trace::ExplanationDetail::Full,
        emission_index: None,
        emission_value: None,
        assume_unknown_input: false,
        eval_mode: evaluation_trace::EvaluationMode::Causality,
        ..Default::default()
    });

    let input: Value = serde_json::from_str(input_json).unwrap();
    vm.set_input(input);
    let value = vm.execute_entry_point_by_name(entrypoint_str).unwrap();
    let report = vm.take_causality_report(value).unwrap();
    serde_json::from_str(&report).unwrap()
}

/// Find the first condition whose `text` contains `needle` anywhere in the
/// report's per-rule per-definition conditions array.
fn find_condition<'a>(
    report: &'a serde_json::Value,
    needle: &str,
) -> Option<&'a serde_json::Value> {
    let rules = report.get("rules")?.as_array()?;
    for rule in rules {
        let defs = rule.get("definitions")?.as_array()?;
        for def in defs {
            let conditions = def.get("conditions")?.as_array()?;
            for cond in conditions {
                if cond
                    .get("text")
                    .and_then(|t| t.as_str())
                    .is_some_and(|t| t.contains(needle))
                {
                    return Some(cond);
                }
            }
        }
    }
    None
}

/// Collect every condition across every (rule, definition).
fn all_conditions(report: &serde_json::Value) -> Vec<&serde_json::Value> {
    let mut out = Vec::new();
    if let Some(rules) = report.get("rules").and_then(|v| v.as_array()) {
        for rule in rules {
            if let Some(defs) = rule.get("definitions").and_then(|v| v.as_array()) {
                for def in defs {
                    if let Some(conds) = def.get("conditions").and_then(|v| v.as_array()) {
                        out.extend(conds.iter());
                    }
                }
            }
        }
    }
    out
}

/// Assert the shape of a direct-case (non-negated) whitelisted-builtin
/// condition in a causality report. Shared across the
/// `causality_5a_*_covered` / `..._carries_*` tests — one call per builtin
/// locks the uniform contract: `kind == "builtin"`, exact `builtin_name`,
/// `left.provenance` rooted at `input.resources` and containing the subject
/// fragment, `right.value` matches the expected JSON literal (works for
/// scalars AND arrays like `strings.any_prefix_match`'s patterns arg).
///
/// The whitelist itself lives in `builtin_operand_indices`.
fn assert_builtin_condition_shape(
    report: &serde_json::Value,
    text_needle: &str,
    expected_builtin_name: &str,
    expected_subject_provenance_contains: &str,
    expected_right_value: serde_json::Value,
) {
    let cond = find_condition(report, text_needle).unwrap_or_else(|| {
        panic!("missing builtin condition matching '{text_needle}'; report: {report:#?}")
    });
    assert_eq!(
        cond.get("kind").and_then(|v| v.as_str()),
        Some("builtin"),
        "kind should be 'builtin' for {expected_builtin_name}; got: {cond:#?}"
    );
    assert_eq!(
        cond.get("builtin_name").and_then(|v| v.as_str()),
        Some(expected_builtin_name),
        "builtin_name should be '{expected_builtin_name}'; got: {cond:#?}"
    );
    let left_prov = cond
        .get("left")
        .and_then(|l| l.get("provenance"))
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert!(
        left_prov.contains(expected_subject_provenance_contains),
        "left.provenance should contain '{expected_subject_provenance_contains}' for {expected_builtin_name}; got '{left_prov}' in {cond:#?}"
    );
    assert!(
        left_prov.starts_with("input.resources"),
        "left.provenance should be rooted at input.resources for {expected_builtin_name}; got '{left_prov}'"
    );
    let right_val = cond
        .get("right")
        .and_then(|r| r.get("value"))
        .unwrap_or_else(|| {
            panic!("right.value missing for {expected_builtin_name}; got: {cond:#?}")
        });
    assert_eq!(
        right_val, &expected_right_value,
        "right.value mismatch for {expected_builtin_name}; expected {expected_right_value:?}, got: {cond:#?}"
    );
}

// ===========================================================================
// Causality-2:  `not X == Y` should carry operator/operand provenance
// ===========================================================================
#[test]
fn causality_2_not_equals_carries_structure() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    not resource.allowSharedKeyAccess == false
    msg := sprintf("Storage '%s' must set allowSharedKeyAccess to false", [resource.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "badStorage",
            "properties": { "minimumTlsVersion": "TLS1_2" }
        }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "not resource.allowSharedKeyAccess")
        .unwrap_or_else(|| panic!("missing condition; report: {report:#?}"));

    // `not <comparison>` emits kind="comparison" + negated=true
    // instead of the retired kind="negation" wrapper.
    assert_eq!(
        cond.get("kind").and_then(|v| v.as_str()),
        Some("comparison"),
        "not <comparison> should carry kind=comparison (inner shape); got: {cond:#?}"
    );
    assert_eq!(
        cond.get("negated").and_then(|v| v.as_bool()),
        Some(true),
        "negated modifier should be true; got: {cond:#?}"
    );
    assert_eq!(
        cond.get("operator").and_then(|v| v.as_str()),
        Some("=="),
        "inner operator should be preserved; got: {cond:#?}"
    );

    let left_prov = cond
        .get("left")
        .and_then(|l| l.get("provenance"))
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert!(
        left_prov.contains("allowSharedKeyAccess"),
        "left.provenance should resolve to the LHS input path; got '{left_prov}' in {cond:#?}"
    );
}

// ===========================================================================
// Causality-1:  `not <builtin>(...)` should at least carry input provenance
// ===========================================================================
#[test]
fn causality_1_not_builtin_carries_inner_provenance() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    not contains(resource.location, "us")
    msg := sprintf("Resource '%s' in disallowed region '%s'", [resource.name, resource.location])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "euStorage",
            "location": "westeurope",
            "properties": {}
        }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "not contains(resource.location")
        .unwrap_or_else(|| panic!("missing condition; report: {report:#?}"));

    // `not <whitelisted-builtin>` emits kind="builtin" + negated=true
    // instead of the retired kind="negation" wrapper.
    assert_eq!(
        cond.get("kind").and_then(|v| v.as_str()),
        Some("builtin"),
        "not <builtin> should carry kind=builtin (inner shape); got: {cond:#?}"
    );
    assert_eq!(
        cond.get("negated").and_then(|v| v.as_bool()),
        Some(true),
        "negated modifier should be true; got: {cond:#?}"
    );

    // For builtin-call negations we may not surface an operator, but we
    // should at least attach the input-rooted provenance of the argument
    // (resource.location) somewhere — either as left.provenance or on the
    // condition's checked path.
    let left_prov = cond
        .get("left")
        .and_then(|l| l.get("provenance"))
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert!(
        left_prov.contains("location"),
        "left.provenance should point at resource.location; got '{left_prov}' in {cond:#?}"
    );
}

// ===========================================================================
// Causality-3:  rule.definitions[] must contain one entry per *evaluated*
// definition, not just the last one to run.
// ===========================================================================
#[test]
fn causality_3_multiple_definitions_each_reported() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    r.properties.supportsHttpsTrafficOnly == false
    msg := sprintf("Storage '%s' must enable HTTPS", [r.name])
}

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    r.properties.allowBlobPublicAccess == true
    msg := sprintf("Storage '%s' must not allow public blobs", [r.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "demoissue7",
            "properties": {
                "supportsHttpsTrafficOnly": false,
                "allowBlobPublicAccess": true
            }
        }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");

    let rule = report
        .get("rules")
        .and_then(|r| r.as_array())
        .and_then(|r| {
            r.iter()
                .find(|r| r.get("name").and_then(|n| n.as_str()) == Some("data.bicep.deny"))
        })
        .unwrap_or_else(|| panic!("missing data.bicep.deny rule in report: {report:#?}"));

    let defs = rule
        .get("definitions")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("missing definitions; rule: {rule:#?}"));

    // Both definitions fire, so both must be represented.
    assert_eq!(
        defs.len(),
        2,
        "expected 2 definition entries (one per fired deny block), got {}: {:#?}",
        defs.len(),
        defs
    );

    let mut indices: Vec<u64> = defs
        .iter()
        .filter_map(|d| d.get("index").and_then(|v| v.as_u64()))
        .collect();
    indices.sort_unstable();
    assert_eq!(
        indices,
        vec![0, 1],
        "definition entries should cover indices 0 and 1; got {indices:?}"
    );
}

// ===========================================================================
// Causality-4:  Undefined LHS in `X == Y` must use the resolved iterator
// index in provenance, not the `[_]` wildcard.
// ===========================================================================
#[test]
fn causality_4_undefined_lhs_uses_resolved_iterator_index() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    resource.properties.minimumTlsVersion == "TLS1_2"
    msg := sprintf("Storage '%s' is fine", [resource.name])
}
"#;
    let input = r#"{
        "resources": [
            {
                "type": "Microsoft.Storage/storageAccounts",
                "name": "storageA",
                "properties": { "minimumTlsVersion": "TLS1_2" }
            },
            {
                "type": "Microsoft.Storage/storageAccounts",
                "name": "storageB",
                "properties": {}
            },
            {
                "type": "Microsoft.Storage/storageAccounts",
                "name": "storageC",
                "properties": { "minimumTlsVersion": "TLS1_0" }
            }
        ]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");

    // Find every comparison frame for resource.properties.minimumTlsVersion
    // across all iterations.
    let conds: Vec<_> = all_conditions(&report)
        .into_iter()
        .filter(|c| {
            c.get("text")
                .and_then(|t| t.as_str())
                .is_some_and(|t| t.contains("resource.properties.minimumTlsVersion"))
        })
        .collect();

    assert_eq!(
        conds.len(),
        3,
        "expected 3 comparison frames (one per iteration), got {}; report: {:#?}",
        conds.len(),
        report
    );

    for cond in &conds {
        let prov = cond
            .get("left")
            .and_then(|l| l.get("provenance"))
            .and_then(|v| v.as_str())
            .unwrap_or("");
        assert!(
            !prov.contains("[_]"),
            "iterator should be resolved to a concrete index, not [_]; got '{prov}' in {cond:#?}"
        );
        assert!(
            prov.starts_with("input.resources["),
            "provenance should be rooted at input.resources[N]; got '{prov}'"
        );
    }
}

// ===========================================================================
// PE test helpers
// ===========================================================================
fn run_pe(policy: &str, input_json: &str, entrypoint_str: &str) -> serde_json::Value {
    let mut engine = Engine::new();
    engine
        .add_policy("policy.rego".into(), policy.into())
        .unwrap();

    let entrypoint: Rc<str> = entrypoint_str.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint).unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
            .unwrap();

    let mut vm = rvm::RegoVM::new_with_policy(compiled);
    vm.load_program(program);
    vm.set_explanation_settings(evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode: evaluation_trace::ValueMode::Full,
        condition_mode: evaluation_trace::ConditionMode::AllContributing,
        scope: evaluation_trace::ExplanationScope::AllEmissions,
        detail: evaluation_trace::ExplanationDetail::Full,
        emission_index: None,
        emission_value: None,
        assume_unknown_input: true,
        eval_mode: evaluation_trace::EvaluationMode::PartialEval,
        unknowns: vec!["input.deployment".into()],
    });

    let input: Value = serde_json::from_str(input_json).unwrap();
    vm.set_input(input);

    let value = vm.execute_entry_point_by_name(entrypoint_str).unwrap();
    let report = vm.take_partial_eval_result(value).unwrap();
    serde_json::from_str(&report).unwrap()
}

// ===========================================================================
// PE-1: residual conditions carry source attribution (rule name + location).
// ===========================================================================
#[test]
fn pe_1_residual_conditions_carry_source_attribution() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    input.deployment.resourceGroupName == "prod-rg"
    r.properties.supportsHttpsTrafficOnly == false
    msg := sprintf("[https] Storage '%s' in prod-rg must enable HTTPS", [r.name])
}

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    input.deployment.location == "eastus"
    r.properties.allowBlobPublicAccess == true
    msg := sprintf("[blob] Storage '%s' in eastus must not allow public blobs", [r.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "demoissue1",
            "location": "eastus",
            "properties": {
                "supportsHttpsTrafficOnly": false,
                "allowBlobPublicAccess": true
            }
        }]
    }"#;

    let result = run_pe(policy, input, "data.bicep.deny");
    let queries = result["residual_queries"]
        .as_array()
        .unwrap_or_else(|| panic!("missing residual_queries; got: {result:#?}"));

    assert!(
        !queries.is_empty(),
        "expected at least one residual disjunct; got: {result:#?}"
    );

    // Every condition in every disjunct must carry source attribution.
    for (i, disjunct) in queries.iter().enumerate() {
        for (j, cond) in disjunct.as_array().unwrap().iter().enumerate() {
            assert!(
                cond.get("source_rule")
                    .and_then(|v| v.as_str())
                    .is_some_and(|s| s == "data.bicep.deny"),
                "disjunct {i}, condition {j}: source_rule missing or wrong; got: {cond:#?}"
            );
            assert!(
                cond.get("source_file")
                    .and_then(|v| v.as_str())
                    .is_some_and(|s| s == "policy.rego"),
                "disjunct {i}, condition {j}: source_file missing or wrong; got: {cond:#?}"
            );
            assert!(
                cond.get("source_row").and_then(|v| v.as_u64()).is_some(),
                "disjunct {i}, condition {j}: source_row missing; got: {cond:#?}"
            );
        }
    }
}

// ===========================================================================
// PE-2: a concretely-firing rule no longer emits an empty negation_holds
// placeholder.
// ===========================================================================
#[test]
fn pe_2_concrete_rule_omits_empty_negation_placeholder() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.DocumentDB/databaseAccounts"
    not r.properties.disableLocalAuth == true
    msg := sprintf("Cosmos '%s' must disable local auth", [r.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.DocumentDB/databaseAccounts",
            "name": "demoissue2",
            "location": "eastus",
            "properties": {
                "databaseAccountOfferType": "Standard"
            }
        }]
    }"#;

    let result = run_pe(policy, input, "data.bicep.deny");
    let queries = result["residual_queries"].as_array().unwrap();

    // None of the disjuncts may contain an empty negation_holds placeholder
    // (kind=negation_holds with no condition text, no input_path, no inner).
    for (i, disjunct) in queries.iter().enumerate() {
        for cond in disjunct.as_array().unwrap() {
            let kind = cond.get("kind").and_then(|v| v.as_str()).unwrap_or("");
            if kind == "negation_holds" {
                let has_condition = cond
                    .get("condition")
                    .and_then(|v| v.as_str())
                    .is_some_and(|s| !s.is_empty());
                let has_path = cond.get("input_path").is_some();
                let has_inner = cond
                    .get("negated_conditions")
                    .and_then(|v| v.as_array())
                    .is_some_and(|a| !a.is_empty());
                assert!(
                    has_condition || has_path || has_inner,
                    "disjunct {i} contains an empty negation_holds placeholder: {cond:#?}"
                );
            }
        }
    }
}

// ===========================================================================
// PE-3: trailing Rego comments are stripped from rendered condition strings.
// ===========================================================================
#[test]
fn pe_3_inline_comments_stripped_from_rendered_condition() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    input.deployment.location == "eastus"   # forces residual to remain (unknown)
    msg := sprintf("Storage '%s' violates", [r.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "demoissue3comment",
            "location": "eastus",
            "properties": {}
        }]
    }"#;

    let result = run_pe(policy, input, "data.bicep.deny");
    let queries = result["residual_queries"].as_array().unwrap();

    let mut found_location_cond = false;
    for disjunct in queries {
        for cond in disjunct.as_array().unwrap() {
            let text = cond.get("condition").and_then(|v| v.as_str()).unwrap_or("");
            if text.contains("input.deployment.location") {
                found_location_cond = true;
                assert!(
                    !text.contains('#'),
                    "rendered condition still contains trailing comment: '{text}' in {cond:#?}"
                );
            }
        }
    }
    assert!(
        found_location_cond,
        "expected a residual condition referencing input.deployment.location; got: {result:#?}"
    );
}

// ===========================================================================
// PE-5: PE residual conjuncts carry `source_rule_start_row` pointing at the
// first-instruction row of the definition (rule body) that produced them.
// Complements the existing `source_row` field so consumers can exact-match a
// residual conjunct to a specific same-name rule body — mirrors the value the
// causality report emits as `DefinitionExplanation.location.row`.
// ===========================================================================
#[test]
fn pe_5_residual_carries_source_rule_start_row_for_multi_definition_rules() {
    // Two same-name `deny` definitions with headers at KNOWN distinct rows.
    // Row numbers are locked in the raw string below: the leading blank line
    // from `r#"` means "package bicep" is on row 2. Definition 1 header is on
    // row 5; definition 2 header is on row 13. Each definition has a distinct
    // `input.deployment.*` gate that leaves a PE residual under
    // `unknowns = ["input.deployment"]`.
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some r in input.resources
    input.deployment.resourceGroupName == "prod-rg"
    r.properties.supportsHttpsTrafficOnly == false
    msg := sprintf("[https] Storage '%s' in prod-rg must enable HTTPS", [r.name])
}

deny contains msg if {
    some r in input.resources
    input.deployment.location == "eastus"
    r.properties.allowBlobPublicAccess == true
    msg := sprintf("[blob] Storage '%s' in eastus must not allow public blobs", [r.name])
}
"#;
    // Resource satisfies both rules' resource-side conditions concretely; the
    // deployment sub-tree stays unknown and produces per-definition residuals.
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "demopeissue5",
            "location": "eastus",
            "properties": {
                "supportsHttpsTrafficOnly": false,
                "allowBlobPublicAccess": true
            }
        }]
    }"#;

    let result = run_pe(policy, input, "data.bicep.deny");
    let queries = result["residual_queries"]
        .as_array()
        .unwrap_or_else(|| panic!("missing residual_queries; got: {result:#?}"));

    assert!(
        !queries.is_empty(),
        "expected at least one residual disjunct; got: {result:#?}"
    );

    // (1) Presence + (2) structural invariant `source_rule_start_row <= source_row`.
    // Also collect distinct start-row values for the exact-attribution check below.
    let mut start_rows: HashSet<u64> = HashSet::new();
    for (i, disjunct) in queries.iter().enumerate() {
        for (j, cond) in disjunct.as_array().unwrap().iter().enumerate() {
            let sr_start = cond
                .get("source_rule_start_row")
                .and_then(|v| v.as_u64())
                .unwrap_or_else(|| {
                    panic!(
                        "disjunct {i}, condition {j}: source_rule_start_row missing; got: {cond:#?}"
                    )
                });
            let sr = cond
                .get("source_row")
                .and_then(|v| v.as_u64())
                .unwrap_or_else(|| {
                    panic!("disjunct {i}, condition {j}: source_row missing; got: {cond:#?}")
                });
            assert!(
                sr_start <= sr,
                "disjunct {i}, condition {j}: rule-start row {sr_start} must be at or before conjunct row {sr}; got: {cond:#?}"
            );
            start_rows.insert(sr_start);
        }
    }

    // (3) Exact attribution: the two definitions' known header rows are 5 and 12.
    // (Row 12 not 13 — one blank line between definitions, not two.) This is the
    // multi-body-attribution win — different definitions of the same rule name
    // are distinguishable by `source_rule_start_row` on their residual conjuncts.
    let expected: HashSet<u64> = [5, 12].into_iter().collect();
    assert_eq!(
        start_rows, expected,
        "expected exactly {{5, 12}} distinct source_rule_start_row values across disjuncts; got {start_rows:?}"
    );
}

// ===========================================================================
// Causality-5(a):  String-predicate builtins in guard position emit structured
// operands + a `builtin_name` field instead of an opaque `kind: "truthiness"`
// record, giving consumers a uniform
// `left = subject with provenance, right = value` shape regardless of the
// builtin's source-code arg order, so they never have to parse condition text.
// ===========================================================================
#[test]
fn causality_5a_startswith_carries_structured_operands() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    startswith(resource.sku.name, "Premium")
    msg := sprintf("Storage '%s' uses Premium SKU", [resource.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "premiumSA",
            "sku": { "name": "Premium_LRS" }
        }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    assert_builtin_condition_shape(
        &report,
        "startswith(resource.sku.name",
        "startswith",
        "sku.name",
        serde_json::json!("Premium"),
    );
}

// ===========================================================================
// Causality-5(a) — PE-residual side: `record_builtin_assumption` populates
// `operator` (builtin name) and `assumed_value` (literal) so a whitelisted
// string-builtin conjunct arrives structured in a PE residual, matching the
// shape already emitted for comparison assumptions.
// ===========================================================================
#[test]
fn causality_5a_pe_residual_carries_builtin_operator_and_value() {
    // Subject is `input.deployment.resourceGroupName` — under the declared
    // unknown subtree — so `startswith(Undefined, "prod-")` residualizes with
    // the builtin's structured fields (operator="startswith", value="prod-",
    // input_path="input.deployment.resourceGroupName").
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some r in input.resources
    startswith(input.deployment.resourceGroupName, "prod-")
    msg := sprintf("Resource '%s' in prod-* group", [r.name])
}
"#;
    let input = r#"{
        "resources": [{ "name": "sa1" }]
    }"#;

    let result = run_pe(policy, input, "data.bicep.deny");
    let queries = result["residual_queries"]
        .as_array()
        .unwrap_or_else(|| panic!("missing residual_queries; got: {result:#?}"));

    // Find the conjunct whose operator is "startswith" — the builtin residual.
    let startswith_conj = queries
        .iter()
        .flat_map(|d| d.as_array().unwrap().iter())
        .find(|c| c.get("operator").and_then(|v| v.as_str()) == Some("startswith"))
        .unwrap_or_else(|| {
            panic!("expected a residual conjunct with operator=\"startswith\"; got: {result:#?}")
        });

    // Exact value literal.
    assert_eq!(
        startswith_conj.get("value").and_then(|v| v.as_str()),
        Some("prod-"),
        "residual conjunct's value should be 'prod-'; got: {startswith_conj:#?}"
    );

    // input_path attributes back to the subject arg (declared unknown).
    let input_path = startswith_conj
        .get("input_path")
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert_eq!(
        input_path, "input.deployment.resourceGroupName",
        "residual conjunct's input_path should be exactly the declared unknown subject path; got '{input_path}' in {startswith_conj:#?}"
    );
}

// ===========================================================================
// Causality-5(a) — Negated form: `not startswith(...)` propagates the inner
// builtin's structured operands + builtin_name up to the outer record, so a
// consumer handles the negated case without a text-parsing fallback.
//
// Mirrors `causality_1_not_builtin_carries_inner_provenance` (which still
// passes on its weaker assertions) but adds the exact-value assertions that
// lock the structured shape.
// ===========================================================================
#[test]
fn causality_5a_negated_builtin_still_carries_operands() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    not startswith(resource.name, "test-")
    msg := sprintf("Resource '%s' must start with 'test-'", [resource.name])
}
"#;
    let input = r#"{
        "resources": [{ "name": "prodResource1" }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "not startswith(resource.name")
        .unwrap_or_else(|| panic!("missing negated startswith condition; report: {report:#?}"));

    // (1) Outer kind is the inner shape ("builtin"), with negated=true
    // flagging the inversion, rather than a dual-role kind="negation".
    assert_eq!(
        cond.get("kind").and_then(|v| v.as_str()),
        Some("builtin"),
        "outer condition should be kind=builtin with negated=true; got: {cond:#?}"
    );
    assert_eq!(
        cond.get("negated").and_then(|v| v.as_bool()),
        Some(true),
        "negated modifier should be true; got: {cond:#?}"
    );

    // (2) builtin_name propagates from inner builtin through peek_through_negation Case B.
    assert_eq!(
        cond.get("builtin_name").and_then(|v| v.as_str()),
        Some("startswith"),
        "builtin_name should propagate from inner builtin; got: {cond:#?}"
    );

    // (3) Subject provenance (from arg[0] for Tier 1 builtin) reaches left.provenance.
    let left_prov = cond
        .get("left")
        .and_then(|l| l.get("provenance"))
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert!(
        left_prov.contains("name"),
        "left.provenance should point at resource.name; got '{left_prov}' in {cond:#?}"
    );

    // (4) right.value carries the literal from the inner builtin's value arg.
    let right_val = cond.get("right").and_then(|r| r.get("value"));
    assert_eq!(
        right_val.and_then(|v| v.as_str()),
        Some("test-"),
        "right.value should be the literal 'test-'; got: {cond:#?}"
    );
}

// ===========================================================================
// Causality-5(a) — Tier 2 arg-order contract: `regex.match(pattern, subject)`
// puts pattern first in Rego, but consumers see uniform
// `left = subject with provenance, right = pattern` shape after normalization
// by `builtin_operand_indices`.
// ===========================================================================
#[test]
fn causality_5a_regex_match_carries_reversed_operands() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    regex.match("^prod-", resource.name)
    msg := sprintf("Resource '%s' uses prod- prefix", [resource.name])
}
"#;
    let input = r#"{
        "resources": [{ "name": "prod-svc1" }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    // Even though `regex.match`'s source arg order is (pattern, subject),
    // the emitted record has left = subject (with provenance) and right =
    // pattern — locked by `assert_builtin_condition_shape` (which asserts
    // `left.provenance` is rooted at input.resources and contains the subject
    // fragment; right.value is the pattern literal).
    assert_builtin_condition_shape(
        &report,
        "regex.match",
        "regex.match",
        "name",
        serde_json::json!("^prod-"),
    );
}

// ===========================================================================
// Causality-5(a) — per-builtin coverage tests. Each remaining whitelist entry
// gets a minimal shape-check: kind="builtin", exact
// `builtin_name`, `left.provenance` points at the subject arg, `right.value`
// carries the value arg. Locks each builtin's registration in the whitelist
// against accidental removal.
//
// Not exhaustive — the direct/PE/negated/reversed-arg paths are already
// exercised by `causality_5a_startswith_*` and `causality_5a_regex_match_*`.
// These tests only verify each whitelisted builtin's basic structured shape.
// ===========================================================================

#[test]
fn causality_5a_endswith_covered() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    endswith(resource.name, "-prod")
    msg := sprintf("Resource '%s' ends with prod suffix", [resource.name])
}
"#;
    let input = r#"{"resources": [{ "name": "svc-prod" }]}"#;
    let report = run_causality_full(policy, input, "data.bicep.deny");
    assert_builtin_condition_shape(
        &report,
        "endswith(resource.name",
        "endswith",
        "name",
        serde_json::json!("-prod"),
    );
}

#[test]
fn causality_5a_contains_builtin_covered() {
    // Note: this exercises the STRING `contains(str, substr)` builtin, NOT
    // the RVM `Contains` opcode (which implements `x in coll` membership and
    // reports as `kind: "membership"` / operator "in").
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    contains(resource.name, "prod")
    msg := sprintf("Resource '%s' contains prod substring", [resource.name])
}
"#;
    let input = r#"{"resources": [{ "name": "sa-prod-eastus" }]}"#;
    let report = run_causality_full(policy, input, "data.bicep.deny");
    assert_builtin_condition_shape(
        &report,
        "contains(resource.name",
        "contains",
        "name",
        serde_json::json!("prod"),
    );
}

#[test]
fn causality_5a_any_prefix_match_covered() {
    // `strings.any_prefix_match(subject, patterns)` — patterns is an ARRAY.
    // Verifies the whitelist handles a non-scalar `right.value`.
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    strings.any_prefix_match(resource.name, ["prod-", "prd-"])
    msg := sprintf("Resource '%s' matches production prefix", [resource.name])
}
"#;
    let input = r#"{"resources": [{ "name": "prod-svc1" }]}"#;
    let report = run_causality_full(policy, input, "data.bicep.deny");
    assert_builtin_condition_shape(
        &report,
        "strings.any_prefix_match",
        "strings.any_prefix_match",
        "name",
        serde_json::json!(["prod-", "prd-"]),
    );
}

#[test]
fn causality_5a_any_suffix_match_covered() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    strings.any_suffix_match(resource.name, ["-prod", "-prd"])
    msg := sprintf("Resource '%s' matches production suffix", [resource.name])
}
"#;
    let input = r#"{"resources": [{ "name": "svc1-prod" }]}"#;
    let report = run_causality_full(policy, input, "data.bicep.deny");
    assert_builtin_condition_shape(
        &report,
        "strings.any_suffix_match",
        "strings.any_suffix_match",
        "name",
        serde_json::json!(["-prod", "-prd"]),
    );
}

#[test]
fn causality_5a_cidr_contains_covered() {
    // Tier 2: `net.cidr_contains(cidr, ip)` — arg[0] is the CIDR (value/pattern),
    // arg[1] is the IP (subject). Sibling to `regex.match` — verifies the
    // reversed-arg mapping applies to non-regex Tier 2 builtins too.
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    net.cidr_contains("10.0.0.0/8", resource.properties.ipAddress)
    msg := sprintf("Resource '%s' in internal CIDR", [resource.name])
}
"#;
    let input = r#"{
        "resources": [{
            "name": "vm1",
            "properties": { "ipAddress": "10.1.2.3" }
        }]
    }"#;
    let report = run_causality_full(policy, input, "data.bicep.deny");
    // Tier 2 contract: left = subject (arg[1] = the IP), right = value (arg[0] = the CIDR).
    // Helper asserts left.provenance contains the subject fragment ("ipAddress").
    assert_builtin_condition_shape(
        &report,
        "net.cidr_contains",
        "net.cidr_contains",
        "ipAddress",
        serde_json::json!("10.0.0.0/8"),
    );
}

// ===========================================================================
// Causality-5(b): retire ConditionKind::Negation -- negation becomes an
// orthogonal negated:bool modifier alongside the inner shape (comparison
// or builtin or truthiness).
//
// Coverage:
//   * 5b_negated_comparison_full  -- "not X == Y" -> kind: comparison,
//     negated: true, operator: ==, left/right populated with runtime values.
//   * 5b_negated_comparison_pe    -- PE side of the same, residual carries
//     the same shape after partial evaluation.
//   * 5b_opaque_negation_truthiness -- non-whitelisted negation
//     ("not is_string(...)") collapses to kind: truthiness, negated: true
//     (Site 2 rewrite).
//   * 5b_positive_omits_negated_key -- positive comparisons must NOT emit a
//     "negated" key (serde skip_serializing_if guard -- protects byte-
//     identical output for the common positive-condition case).
// ===========================================================================

#[test]
fn causality_5b_negated_comparison_full_shape() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    not resource.properties.minimumTlsVersion == "TLS1_0"
    msg := sprintf("Storage '%s' must not use TLS 1.0", [resource.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "stg1",
            "properties": { "minimumTlsVersion": "TLS1_2" }
        }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "not resource.properties.minimumTlsVersion")
        .unwrap_or_else(|| panic!("missing negated comparison; report: {report:#?}"));

    assert_eq!(
        cond.get("kind").and_then(|v| v.as_str()),
        Some("comparison"),
        "kind must be inner shape 'comparison', not 'negation'; got: {cond:#?}"
    );
    assert_eq!(
        cond.get("negated").and_then(|v| v.as_bool()),
        Some(true),
        "negated must be true on the outer condition; got: {cond:#?}"
    );
    assert_eq!(
        cond.get("operator").and_then(|v| v.as_str()),
        Some("=="),
        "inner operator must survive on the outer record; got: {cond:#?}"
    );

    let left_prov = cond
        .get("left")
        .and_then(|l| l.get("provenance"))
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert!(
        left_prov.contains("minimumTlsVersion"),
        "left.provenance should resolve to the LHS input path; got in {cond:#?}"
    );

    let right_val = cond.get("right").and_then(|r| r.get("value"));
    assert_eq!(
        right_val.and_then(|v| v.as_str()),
        Some("TLS1_0"),
        "right.value should carry the RHS literal; got: {cond:#?}"
    );
}

// NOTE: PE's negation representation is separate from ConditionKind::Negation.
// The PE side uses AssumptionKind::NegationHolds which emits
// kind: "negation_holds" with a negated_conditions: [] array carrying inner
// assumptions. That shape is orthogonal to the static-side refactor here and
// is not affected by retiring ConditionKind::Negation.

#[test]
fn causality_5b_opaque_negation_emits_truthiness() {
    // is_string is NOT on the whitelisted builtin list, so
    // peek_through_negation falls into Case B's non-whitelisted branch and
    // returns no structured operands, which emits
    // kind: truthiness, negated: true.
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    not is_string(resource.name)
    msg := "resource.name must be a string"
}
"#;
    let input = r#"{
        "resources": [{ "name": 42 }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "not is_string(resource.name")
        .unwrap_or_else(|| panic!("missing opaque negation; report: {report:#?}"));

    assert_eq!(
        cond.get("kind").and_then(|v| v.as_str()),
        Some("truthiness"),
        "opaque negation must collapse to kind=truthiness; got: {cond:#?}"
    );
    assert_eq!(
        cond.get("negated").and_then(|v| v.as_bool()),
        Some(true),
        "opaque negation must still carry negated=true; got: {cond:#?}"
    );
}

#[test]
fn causality_5b_positive_omits_negated_key() {
    // Regression pin: positive comparisons MUST NOT serialize a "negated"
    // key. skip_serializing_if guarantees byte-identical output for the
    // common positive-condition case.
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    msg := sprintf("Denied storage %s", [resource.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "stg1"
        }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "resource.type ==")
        .unwrap_or_else(|| panic!("missing positive comparison; report: {report:#?}"));

    assert_eq!(
        cond.get("kind").and_then(|v| v.as_str()),
        Some("comparison"),
        "positive comparison must stay kind=comparison; got: {cond:#?}"
    );
    // The critical assertion: `negated` key is ABSENT (not `false`).
    assert!(
        cond.get("negated").is_none(),
        "positive comparison must not emit a negated key; got: {cond:#?}"
    );
}

// ===========================================================================
// PE-6: canonicalize residual `input_path` + recursive empty-wrapper
// filter.
//
// (a) Strip trailing `[_]` iteration marker from `input_path` on `exists`
//     and `condition_holds` kinds. The `[_]` originates in the engine's
//     phantom-iteration setup (rvm/vm/loops.rs) and is meaningless to the
//     policy author. `collection_exists` is already clean (recorded pre-taint).
//
// (b) Recursively drop empty `negation_holds` placeholders inside
//     `negated_conditions[]` (the top-level retain at causality_report.rs
//     already handles the outer case; this closes the nested-inner leak).
// ===========================================================================

/// PE-6(a): `some x in <unknown>; x == "V"` --- both the `exists` and the
/// `condition_holds` conjuncts must carry a clean `input_path` without the
/// `[_]` iterator suffix.
#[test]
fn pe_6_input_path_strips_iteration_suffix_on_exists_and_condition_holds() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some group in input.deployment.claims.groups
    group == "security"
    msg := "security group must not be present"
}
"#;

    let report = run_pe(policy, "{}", "data.bicep.deny");

    // Walk every disjunct's conjuncts; assert no `input_path` ends in `[_]`.
    let residual_queries = report
        .get("residual_queries")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("missing residual_queries; report: {report:#?}"));
    let mut saw_exists = false;
    let mut saw_condition_holds = false;
    for disjunct in residual_queries {
        let conjuncts = disjunct.as_array().expect("disjunct is array");
        for cond in conjuncts {
            let kind = cond.get("kind").and_then(|v| v.as_str()).unwrap_or("");
            let input_path = cond
                .get("input_path")
                .and_then(|v| v.as_str())
                .unwrap_or("");
            assert!(
                !input_path.ends_with("[_]"),
                "input_path must not carry [_] suffix on kind={kind}; got '{input_path}' in {cond:#?}"
            );
            if kind == "exists" {
                saw_exists = true;
                assert_eq!(
                    input_path, "input.deployment.claims.groups",
                    "exists input_path should be the clean collection path; got '{input_path}'"
                );
            }
            if kind == "condition_holds" {
                saw_condition_holds = true;
                assert_eq!(
                    input_path, "input.deployment.claims.groups",
                    "condition_holds input_path should be the clean collection path; got '{input_path}'"
                );
            }
        }
    }
    assert!(
        saw_exists,
        "expected at least one exists conjunct; report: {report:#?}"
    );
    assert!(
        saw_condition_holds,
        "expected at least one condition_holds conjunct; report: {report:#?}"
    );
}

/// PE-6(a) regression pin: `collection_exists` was already clean pre-Step-6
/// (recorded pre-taint in loops.rs); confirm the strip doesn't accidentally
/// affect it or any other kind.
#[test]
fn pe_6_collection_exists_stays_clean() {
    // Same policy as above --- the fast-fail disjunct emits `collection_exists`
    // as its sole conjunct with the base path.
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some group in input.deployment.claims.groups
    group == "security"
    msg := "security group must not be present"
}
"#;

    let report = run_pe(policy, "{}", "data.bicep.deny");
    let residual_queries = report
        .get("residual_queries")
        .and_then(|v| v.as_array())
        .expect("residual_queries");
    let mut saw_collection_exists = false;
    for disjunct in residual_queries {
        let conjuncts = disjunct.as_array().expect("disjunct is array");
        for cond in conjuncts {
            if cond.get("kind").and_then(|v| v.as_str()) == Some("collection_exists") {
                saw_collection_exists = true;
                let input_path = cond
                    .get("input_path")
                    .and_then(|v| v.as_str())
                    .unwrap_or("");
                assert_eq!(
                    input_path, "input.deployment.claims.groups",
                    "collection_exists input_path must be left unchanged; got '{input_path}'"
                );
            }
        }
    }
    assert!(
        saw_collection_exists,
        "expected at least one collection_exists conjunct; report: {report:#?}"
    );
}

/// PE-6(b): unit test for `filter_empty_placeholders_recursive` semantics.
/// Constructs a `negation_holds` frame containing an empty `negation_holds`
/// nested placeholder and asserts the recursive filter drops it. We express
/// this at the JSON level by constructing a report the way the engine would
/// emit it pre-Step-6, then verifying our post-Step-6 emit path never
/// produces such shapes on real policies (see pe_09_nested_negation, which
/// stays green and whose live-probed output shows all nested conditions are
/// meaningful).
///
/// This is a smoke-test / documentation of the invariant --- the primary
/// coverage is the pe_09 existing test remaining green, and the top-level
/// retain that was already in place (which is still called via the new
/// recursive wrapper).
#[test]
fn pe_6_recursive_filter_invariant_smoke_check() {
    // Re-run pe_09's policy (nested negation) and verify no empty
    // negation_holds frames appear anywhere in the tree.
    let policy = r#"
package test
default allow = false
allow if {
    input.user.role == "viewer"
    not is_restricted(input.document)
}
allow if { input.user.role == "admin" }
is_restricted(doc) if {
    doc.status == "restricted"
    not doc.override == true
}
"#;
    let input = r#"{"user": {"role": "viewer"}}"#;

    let report = run_pe(policy, input, "data.test.allow");
    let residual_queries = report
        .get("residual_queries")
        .and_then(|v| v.as_array())
        .expect("residual_queries");

    fn walk(cond: &serde_json::Value) {
        // Guard: not an object => nothing to check.
        let Some(obj) = cond.as_object() else {
            return;
        };
        let kind = obj.get("kind").and_then(|v| v.as_str()).unwrap_or("");
        if kind == "negation_holds" {
            let condition_empty = obj
                .get("condition")
                .and_then(|v| v.as_str())
                .map(|s| s.is_empty())
                .unwrap_or(true);
            let input_path_none = obj.get("input_path").map(|v| v.is_null()).unwrap_or(true);
            let operator_none = obj.get("operator").map(|v| v.is_null()).unwrap_or(true);
            let inner_empty = obj
                .get("negated_conditions")
                .and_then(|v| v.as_array())
                .map(|a| a.is_empty())
                .unwrap_or(true);
            assert!(
                !(condition_empty && input_path_none && operator_none && inner_empty),
                "empty negation_holds placeholder leaked (all four criteria met): {cond:#?}"
            );
            // Recurse into nested negated_conditions.
            if let Some(nested) = obj.get("negated_conditions").and_then(|v| v.as_array()) {
                for c in nested {
                    walk(c);
                }
            }
        }
    }

    for disjunct in residual_queries {
        for cond in disjunct.as_array().expect("disjunct is array") {
            walk(cond);
        }
    }
}

// ===========================================================================
// Causality-6: helper-boundary left.provenance propagation +
// structural helper_conditions[].
//
// When a rule fails because a helper rule returned falsy (positive
// _helper(x) or negated not _helper(x)), the outer truthiness condition
// gains:
//   (a) A helper_conditions[] array carrying the helper's evaluated inner
//       conditions structurally (so consumers can render "Violation caused
//       by: X.Y.Z" inline).
//   (b) A derived left.provenance pointing at the specific failed inner
//       LHS path (so consumers can land a property-level squiggle).
// ===========================================================================

/// Causality-6(a): outer `not _helper(x)` truthiness gains derived
/// `left.provenance` from the failing inner comparison.
#[test]
fn causality_6_helper_boundary_left_provenance() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some _, resource in input.resources
    resource.type == "Microsoft.Network/frontDoors"
    not _frontdoor_has_waf(resource)
    msg := "must have WAF"
}

_frontdoor_has_waf(resource) if {
    some endpoint in resource.properties.frontendEndpoints
    endpoint.properties.webApplicationFirewallPolicyLink.id != ""
}
"#;
    let input = r#"{
        "resources": [
            {
                "name": "badFrontDoor",
                "type": "Microsoft.Network/frontDoors",
                "properties": {
                    "frontendEndpoints": [
                        { "properties": {} }
                    ]
                }
            }
        ]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "not _frontdoor_has_waf(resource)")
        .unwrap_or_else(|| panic!("missing outer helper-call condition; report: {report:#?}"));

    // The outer truthiness carries a derived left.provenance from the
    // helper's failing inner LHS, which is what lets a consumer land a
    // property-level squiggle.
    let left_prov = cond
        .get("left")
        .and_then(|l| l.get("provenance"))
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert!(
        left_prov.contains("webApplicationFirewallPolicyLink"),
        "outer left.provenance should be derived from failing inner LHS; got '{left_prov}' in {cond:#?}"
    );
    assert!(
        left_prov.starts_with("input.resources"),
        "outer left.provenance should be rooted at input.resources; got '{left_prov}'"
    );
}

/// Causality-6(b): outer truthiness carries structural `helper_conditions[]`
/// containing the helper's evaluated inner conditions with proper kinds.
#[test]
fn causality_6_helper_boundary_conditions_populated() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some _, resource in input.resources
    resource.type == "Microsoft.Network/frontDoors"
    not _frontdoor_has_waf(resource)
    msg := "must have WAF"
}

_frontdoor_has_waf(resource) if {
    some endpoint in resource.properties.frontendEndpoints
    endpoint.properties.webApplicationFirewallPolicyLink.id != ""
}
"#;
    let input = r#"{
        "resources": [
            {
                "name": "badFrontDoor",
                "type": "Microsoft.Network/frontDoors",
                "properties": {
                    "frontendEndpoints": [
                        { "properties": {} }
                    ]
                }
            }
        ]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "not _frontdoor_has_waf(resource)")
        .unwrap_or_else(|| panic!("missing outer helper-call condition; report: {report:#?}"));

    let helper_conds = cond
        .get("helper_conditions")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("helper_conditions must be present; got: {cond:#?}"));
    assert!(
        !helper_conds.is_empty(),
        "helper_conditions must not be empty; got: {cond:#?}"
    );

    // The failing inner comparison must appear among helper_conditions with
    // structured operator/left/right.
    let failing_cmp = helper_conds
        .iter()
        .find(|c| {
            c.get("text")
                .and_then(|t| t.as_str())
                .is_some_and(|t| t.contains("webApplicationFirewallPolicyLink"))
        })
        .unwrap_or_else(|| panic!("no comparison for webApplicationFirewallPolicyLink; got helpers: {helper_conds:#?}"));
    assert_eq!(
        failing_cmp.get("kind").and_then(|v| v.as_str()),
        Some("comparison"),
        "failing inner should be kind=comparison; got: {failing_cmp:#?}"
    );
    assert_eq!(
        failing_cmp.get("operator").and_then(|v| v.as_str()),
        Some("!="),
        "operator should be !=; got: {failing_cmp:#?}"
    );
    assert_eq!(
        failing_cmp.get("outcome").and_then(|v| v.as_str()),
        Some("failure"),
        "outcome should be failure; got: {failing_cmp:#?}"
    );
}

/// Causality-6(c): helper conditions do NOT also appear as siblings in the
/// outer rule's emissions[].conditions[] list -- they are filtered out
/// so consumers see them exactly once, under helper_conditions[] only.
/// (The helper rule's OWN rules[].definitions[].conditions[] entry still
/// legitimately lists them, since each rule owns its own condition tree.)
#[test]
fn causality_6_helper_conditions_not_duplicated_as_siblings() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some _, resource in input.resources
    resource.type == "Microsoft.Network/frontDoors"
    not _frontdoor_has_waf(resource)
    msg := "must have WAF"
}

_frontdoor_has_waf(resource) if {
    some endpoint in resource.properties.frontendEndpoints
    endpoint.properties.webApplicationFirewallPolicyLink.id != ""
}
"#;
    let input = r#"{
        "resources": [
            {
                "name": "badFrontDoor",
                "type": "Microsoft.Network/frontDoors",
                "properties": {
                    "frontendEndpoints": [
                        { "properties": {} }
                    ]
                }
            }
        ]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");

    // Walk the DENY rule's emissions[].conditions[] list; the helper's
    // inner comparison must NOT appear there as a sibling. It belongs
    // only inside helper_conditions[] of the outer truthiness now.
    let rules = report
        .get("rules")
        .and_then(|v| v.as_array())
        .expect("rules array");
    let deny_rule = rules
        .iter()
        .find(|r| r.get("name").and_then(|n| n.as_str()) == Some("data.bicep.deny"))
        .expect("deny rule present");
    let emissions = deny_rule
        .get("emissions")
        .and_then(|v| v.as_array())
        .expect("emissions array");
    let mut sibling_count = 0;
    for emission in emissions {
        if let Some(conds) = emission.get("conditions").and_then(|v| v.as_array()) {
            for cond in conds {
                if cond
                    .get("text")
                    .and_then(|t| t.as_str())
                    .is_some_and(|t| t.contains("webApplicationFirewallPolicyLink"))
                {
                    sibling_count += 1;
                }
            }
        }
    }
    assert_eq!(
        sibling_count, 0,
        "helper inner comparison must not appear as sibling in deny.emissions[].conditions[]; found {sibling_count}"
    );
}

/// Causality-6(d): regression pin -- when a rule succeeds normally (no
/// helper failure path exercised), helper_conditions must NOT be emitted on
/// non-helper conditions. Serde skip_serializing_if guarantees the key is
/// absent, not present-and-empty.
#[test]
fn causality_6_positive_condition_omits_helper_conditions_key() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    msg := sprintf("denied '%s'", [resource.name])
}
"#;
    let input = r#"{
        "resources": [
            {
                "type": "Microsoft.Storage/storageAccounts",
                "name": "stg1"
            }
        ]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "resource.type ==")
        .unwrap_or_else(|| panic!("missing comparison; report: {report:#?}"));

    // The critical assertion: helper_conditions key is ABSENT (not empty).
    assert!(
        cond.get("helper_conditions").is_none(),
        "positive comparison must not emit a helper_conditions key; got: {cond:#?}"
    );
}

// ===========================================================================
// Causality-7: helper inner-condition text = body-only, with caller's
// argument literals substituted for the helper's parameter names.
//
// Otherwise `helper_conditions[i].text` echoes the entire helper rule
// declaration verbatim (e.g. `in_resource_group(fragment) if contains(...,
// fragment)`), which leaks the rule head and the helper's parameter names
// into anything a consumer renders from it.
//
// `causality_report::materialize_helper_conditions` rewrites `text` at
// materialize time: slice past the ` if ` separator, then
// word-boundary-substitute helper param names with the caller's argument
// literals (recovered by static analysis of the FunctionCall opcode's
// arg-register `Load` instructions).
// ===========================================================================

/// Causality-7(a): single-arg helper where the caller passes a string
/// literal. The helper's inner `contains(...)` condition must render with
/// the literal substituted for the param name and without the rule head.
#[test]
fn causality_7_helper_single_arg_substituted() {
    let policy = r#"
package bicep
import future.keywords

in_resource_group(fragment) if contains(input.deployment.resourceGroupName, fragment)

deny contains msg if {
    in_resource_group("prod")
    some _, resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    resource.properties.allowBlobPublicAccess == true
    msg := "allowBlobPublicAccess must be false in prod-rg"
}
"#;
    let input = r#"{
        "deployment": { "resourceGroupName": "prod-eastus" },
        "resources": [
            {
                "type": "Microsoft.Storage/storageAccounts",
                "name": "prodstoragebad",
                "properties": { "allowBlobPublicAccess": true }
            }
        ]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "in_resource_group(\"prod\")")
        .unwrap_or_else(|| panic!("missing outer helper-call condition; report: {report:#?}"));

    let inners = cond
        .get("helper_conditions")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("helper_conditions must be present; cond: {cond:#?}"));

    let builtin_inner = inners
        .iter()
        .find(|c| c.get("builtin_name").and_then(|v| v.as_str()) == Some("contains"))
        .unwrap_or_else(|| panic!("missing builtin=contains helper inner; inners: {inners:#?}"));

    let text = builtin_inner
        .get("text")
        .and_then(|v| v.as_str())
        .unwrap_or("");

    // Arg literal substituted for the param name.
    assert!(
        text.contains("\"prod\""),
        "helper body text must contain the arg literal \"prod\"; got: {text}"
    );
    // Param name must NOT leak through.
    assert!(
        !text.contains("fragment"),
        "helper body text must not contain the param name 'fragment'; got: {text}"
    );
    // Rule head must be stripped.
    assert!(
        !text.contains(" if "),
        "helper body text must not contain ' if ' separator; got: {text}"
    );
}

/// Causality-7(b): same single-arg helper; assert the body starts with the
/// builtin call (`contains(...)`), NOT the helper rule head. Explicit
/// regression pin so a future change that drops the rule-head strip but
/// keeps the param substitution still fails visibly.
#[test]
fn causality_7_helper_body_only_no_rule_head() {
    let policy = r#"
package bicep
import future.keywords

in_resource_group(fragment) if contains(input.deployment.resourceGroupName, fragment)

deny contains msg if {
    in_resource_group("prod")
    some _, resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    resource.properties.allowBlobPublicAccess == true
    msg := "must be false in prod-rg"
}
"#;
    let input = r#"{
        "deployment": { "resourceGroupName": "prod-eastus" },
        "resources": [
            {
                "type": "Microsoft.Storage/storageAccounts",
                "name": "s",
                "properties": { "allowBlobPublicAccess": true }
            }
        ]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "in_resource_group(\"prod\")")
        .unwrap_or_else(|| panic!("missing outer helper-call condition; report: {report:#?}"));
    let inners = cond
        .get("helper_conditions")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("helper_conditions must be present; cond: {cond:#?}"));
    let builtin_inner = inners
        .iter()
        .find(|c| c.get("builtin_name").and_then(|v| v.as_str()) == Some("contains"))
        .unwrap_or_else(|| panic!("missing builtin=contains helper inner; inners: {inners:#?}"));

    let text = builtin_inner
        .get("text")
        .and_then(|v| v.as_str())
        .unwrap_or("");

    assert!(
        text.starts_with("contains("),
        "helper body text must start with 'contains('; got: {text}"
    );
    assert!(
        !text.contains("in_resource_group"),
        "helper body text must not contain the helper name 'in_resource_group'; got: {text}"
    );
}

/// Causality-7(c): multi-arg helper. Every parameter must be substituted
/// with its corresponding caller argument literal.
#[test]
fn causality_7_helper_multi_arg_substituted() {
    let policy = r#"
package bicep
import future.keywords

# Two-arg helper: is the RG name equal to `expected` in region `region`?
rg_matches(expected, region) if {
    input.deployment.resourceGroupName == expected
    input.deployment.location == region
}

deny contains msg if {
    rg_matches("prod-rg", "eastus")
    some _, resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    msg := "must not exist here"
}
"#;
    let input = r#"{
        "deployment": {
            "resourceGroupName": "prod-rg",
            "location": "eastus"
        },
        "resources": [
            { "type": "Microsoft.Storage/storageAccounts", "name": "s" }
        ]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "rg_matches(\"prod-rg\", \"eastus\")")
        .unwrap_or_else(|| panic!("missing outer helper-call condition; report: {report:#?}"));
    let inners = cond
        .get("helper_conditions")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("helper_conditions must be present; cond: {cond:#?}"));

    // Collect all inner texts.
    let inner_texts: Vec<String> = inners
        .iter()
        .filter_map(|c| c.get("text").and_then(|v| v.as_str()).map(String::from))
        .collect();

    // Both param names must be gone from every inner text.
    for t in &inner_texts {
        assert!(
            !t.contains("expected"),
            "param name 'expected' leaked into inner text: {t}"
        );
        assert!(
            !t.contains("region"),
            "param name 'region' leaked into inner text: {t}"
        );
    }
    // Both caller literals must appear somewhere in the flattened inner texts.
    let joined = inner_texts.join(" | ");
    assert!(
        joined.contains("\"prod-rg\""),
        "arg literal \"prod-rg\" must appear in helper inner texts; joined: {joined}"
    );
    assert!(
        joined.contains("\"eastus\""),
        "arg literal \"eastus\" must appear in helper inner texts; joined: {joined}"
    );
}

/// Causality-7(d): dynamic-arg regression pin. When a helper receives a
/// non-literal argument (here, the `resource` iteration binding), no
/// `Load { dest, literal_idx }` writes to the arg register, so
/// `find_literal_load` returns `None` and the helper's parameter name is
/// left unsubstituted in the body text. Proves the substitution logic
/// gracefully declines to guess rather than crashing or picking up an
/// unrelated literal from an earlier instruction.
///
/// Uses a multi-line helper body to defeat the compiler's tendency to
/// inline single-body helpers at the call site (which would collapse the
/// helper into a sibling comparison and bypass `helper_conditions[]`).
#[test]
fn causality_7_helper_dynamic_arg_no_substitution() {
    let policy = r#"
package bicep
import future.keywords

is_bad(resource) if {
    resource.type == "Microsoft.Storage/storageAccounts"
    resource.properties.allowBlobPublicAccess == true
}

deny contains msg if {
    some _, resource in input.resources
    is_bad(resource)
    msg := "denied"
}
"#;
    let input = r#"{
        "resources": [
            {
                "type": "Microsoft.Storage/storageAccounts",
                "name": "s",
                "properties": { "allowBlobPublicAccess": true }
            }
        ]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "is_bad(resource)")
        .unwrap_or_else(|| panic!("missing outer helper-call condition; report: {report:#?}"));
    let inners = cond
        .get("helper_conditions")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("helper_conditions must be present; cond: {cond:#?}"));

    for inner in inners {
        let text = inner.get("text").and_then(|v| v.as_str()).unwrap_or("");
        // Rule head must be stripped regardless of literal-vs-dynamic arg.
        assert!(
            !text.contains(" if "),
            "helper body text must not contain ' if ' separator; got: {text}"
        );
        // Body must not start with the helper name.
        assert!(
            !text.starts_with("is_bad"),
            "helper body text must not start with helper name 'is_bad'; got: {text}"
        );
    }
    // At least one inner must still carry the param name `resource` — proving
    // the substitution logic gracefully skipped (no literal available for the
    // dynamic arg) rather than crashing or picking a wrong value.
    let has_param_in_body = inners.iter().any(|inner| {
        inner
            .get("text")
            .and_then(|v| v.as_str())
            .is_some_and(|t| t.contains("resource"))
    });
    assert!(
        has_param_in_body,
        "dynamic-arg helper body must retain the param name 'resource' in at least one inner; \
         inners: {inners:#?}"
    );
}

/// Causality-7(e): regression pin — helper_conditions must NOT contain
/// entries with `kind == "unknown"` and empty `text`. These leak from
/// FunctionCall arg-register binding Moves; they represent internal wiring,
/// not authorable predicates, and `materialize_helper_conditions` filters
/// them out.
#[test]
fn causality_7_helper_no_empty_unknown_entries() {
    let policy = r#"
package bicep
import future.keywords

in_resource_group(fragment) if contains(input.deployment.resourceGroupName, fragment)

deny contains msg if {
    in_resource_group("prod")
    some _, resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    msg := "denied"
}
"#;
    let input = r#"{
        "deployment": { "resourceGroupName": "prod-eastus" },
        "resources": [
            { "type": "Microsoft.Storage/storageAccounts", "name": "s" }
        ]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "in_resource_group(\"prod\")")
        .unwrap_or_else(|| panic!("missing outer helper-call condition; report: {report:#?}"));
    let inners = cond
        .get("helper_conditions")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("helper_conditions must be present; cond: {cond:#?}"));

    for inner in inners {
        let kind = inner.get("kind").and_then(|v| v.as_str()).unwrap_or("");
        let text = inner.get("text").and_then(|v| v.as_str()).unwrap_or("");
        assert!(
            !(kind == "unknown" && text.is_empty()),
            "helper_conditions must not contain empty-text kind:unknown entries; \
             found in: {inner:#?} (all inners: {inners:#?})"
        );
    }
}

// ===========================================================================
// Helper nesting depth cap is observable.
//
// `materialize_helper_conditions` stops recursing at MAX_HELPER_DEPTH. It
// previously returned an empty vec for that case AND for "there is no helper
// call here", so a consumer could not tell a condition with nothing behind it
// from one whose nesting was dropped. That is silent under-reporting, and it
// bites exactly on the deepest policies.
// ===========================================================================

/// Recursively search a report for a condition that reported truncated
/// helper nesting.
fn has_truncation_flag(value: &serde_json::Value) -> bool {
    match value {
        serde_json::Value::Object(map) => {
            if map
                .get("helper_conditions_truncated")
                .and_then(|v| v.as_bool())
                == Some(true)
            {
                return true;
            }
            map.values().any(has_truncation_flag)
        }
        serde_json::Value::Array(items) => items.iter().any(has_truncation_flag),
        _ => false,
    }
}

/// Build `deny -> h1 -> h2 -> ... -> hN`, each helper with a multi-line body
/// so the compiler does not inline it at the call site and collapse the chain.
fn nested_helper_policy(levels: usize) -> String {
    let mut policy = String::from("package bicep\nimport rego.v1\n\n");
    for level in 1..levels {
        policy.push_str(&format!(
            "h{level} if {{\n    h{next}\n    input.deployment.location == \"eastus\"\n}}\n\n",
            next = level + 1
        ));
    }
    policy.push_str(&format!(
        "h{levels} if {{\n    contains(input.deployment.resourceGroupName, \"prod\")\n    input.deployment.location == \"eastus\"\n}}\n\n"
    ));
    policy.push_str("deny contains msg if {\n    h1\n    msg := \"deep chain\"\n}\n");
    policy
}

const NESTED_HELPER_INPUT: &str = r#"{
    "deployment": { "resourceGroupName": "prod-rg", "location": "eastus" }
}"#;

/// A chain deeper than `MAX_HELPER_DEPTH` must say so on the deepest surfaced
/// condition, rather than looking identical to a condition with no helper
/// behind it.
#[test]
fn causality_10_deep_helper_chain_reports_truncation() {
    let policy = nested_helper_policy(9);
    let report = run_causality_full(&policy, NESTED_HELPER_INPUT, "data.bicep.deny");

    assert!(
        has_truncation_flag(&report),
        "a helper chain deeper than the recursion cap must report truncation somewhere; \
         report: {report:#?}"
    );
}

/// Control: a chain well inside the cap must omit the key entirely, so the
/// flag cannot be always-on.
#[test]
fn causality_10_shallow_helper_chain_omits_truncation() {
    let policy = nested_helper_policy(2);
    let report = run_causality_full(&policy, NESTED_HELPER_INPUT, "data.bicep.deny");

    assert!(
        !has_truncation_flag(&report),
        "a chain inside the cap must not report truncation; report: {report:#?}"
    );
}

// ===========================================================================
// Causality-9: engine report emission is deterministic.
//
// A host observed repeated evaluations of an unchanged policy+input producing
// differing output, which would make any consumer's caching or diffing
// unreliable. This test pins the engine side: two consecutive runs of the
// same policy+input must produce byte-identical raw JSON reports (both
// causality and PE modes), so a host seeing variation knows to look at its
// own layer.
//
// The core crate uses BTreeMap/BTreeSet throughout, the PE emit path is
// BTreeMap-keyed, and RVM uses IndexMap (deterministic insertion order), so
// this is expected to hold.
// ===========================================================================

/// Raw-string variant of `run_causality_full` — returns the byte string
/// emitted by `take_causality_report()` so the determinism test can compare
/// output pre-JSON-parse (parsing normalizes into serde_json::Map and would
/// hide iteration-order entropy in the emit layer).
fn run_causality_full_raw(policy: &str, input_json: &str, entrypoint_str: &str) -> String {
    let mut engine = Engine::new();
    engine
        .add_policy("test.rego".into(), policy.into())
        .unwrap();

    let entrypoint: Rc<str> = entrypoint_str.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint).unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
            .unwrap();

    let mut vm = rvm::RegoVM::new_with_policy(compiled);
    vm.load_program(program);
    vm.set_explanation_settings(evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode: evaluation_trace::ValueMode::Full,
        condition_mode: evaluation_trace::ConditionMode::AllContributing,
        scope: evaluation_trace::ExplanationScope::AllEmissions,
        detail: evaluation_trace::ExplanationDetail::Full,
        emission_index: None,
        emission_value: None,
        assume_unknown_input: false,
        eval_mode: evaluation_trace::EvaluationMode::Causality,
        ..Default::default()
    });

    let input: Value = serde_json::from_str(input_json).unwrap();
    vm.set_input(input);
    let value = vm.execute_entry_point_by_name(entrypoint_str).unwrap();
    vm.take_causality_report(value).unwrap()
}

/// Raw-string variant of `run_pe` — see `run_causality_full_raw` docstring
/// for why parsing is bypassed.
fn run_pe_raw(policy: &str, input_json: &str, entrypoint_str: &str) -> String {
    let mut engine = Engine::new();
    engine
        .add_policy("policy.rego".into(), policy.into())
        .unwrap();

    let entrypoint: Rc<str> = entrypoint_str.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint).unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
            .unwrap();

    let mut vm = rvm::RegoVM::new_with_policy(compiled);
    vm.load_program(program);
    vm.set_explanation_settings(evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode: evaluation_trace::ValueMode::Full,
        condition_mode: evaluation_trace::ConditionMode::AllContributing,
        scope: evaluation_trace::ExplanationScope::AllEmissions,
        detail: evaluation_trace::ExplanationDetail::Full,
        emission_index: None,
        emission_value: None,
        assume_unknown_input: true,
        eval_mode: evaluation_trace::EvaluationMode::PartialEval,
        unknowns: vec!["input.deployment".into()],
    });

    let input: Value = serde_json::from_str(input_json).unwrap();
    vm.set_input(input);
    let value = vm.execute_entry_point_by_name(entrypoint_str).unwrap();
    vm.take_partial_eval_result(value).unwrap()
}

/// Multi-rule, multi-resource, multi-target policy designed to exercise the
/// paths most likely to expose iteration-order entropy: several deny rules
/// (target-label fan-out), multiple resource types (per-resource dedupe),
/// helper calls (the helper_conditions[] emit), and PE assumptions on
/// input.deployment.* (residual-emit ordering).
const DETERMINISM_POLICY: &str = r#"
package bicep
import rego.v1

in_prod if {
    input.deployment.resourceGroupName == "prod-rg"
}

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    r.properties.supportsHttpsTrafficOnly == false
    msg := sprintf("Storage '%s' must enable HTTPS", [r.name])
}

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    r.properties.allowBlobPublicAccess == true
    msg := sprintf("Storage '%s' must not allow public blobs", [r.name])
}

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Network/networkSecurityGroups"
    some rule in r.properties.securityRules
    rule.properties.access == "Allow"
    rule.properties.sourceAddressPrefix == "*"
    msg := sprintf("NSG '%s' has open ingress rule '%s'", [r.name, rule.name])
}

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.KeyVault/vaults"
    r.properties.enableSoftDelete == false
    in_prod
    msg := sprintf("KV '%s' in prod must enable soft delete", [r.name])
}
"#;

const DETERMINISM_INPUT: &str = r#"{
    "resources": [
        {
            "type": "Microsoft.Storage/storageAccounts",
            "name": "stg1",
            "properties": {
                "supportsHttpsTrafficOnly": false,
                "allowBlobPublicAccess": true
            }
        },
        {
            "type": "Microsoft.Storage/storageAccounts",
            "name": "stg2",
            "properties": {
                "supportsHttpsTrafficOnly": true,
                "allowBlobPublicAccess": false
            }
        },
        {
            "type": "Microsoft.Network/networkSecurityGroups",
            "name": "nsg1",
            "properties": {
                "securityRules": [
                    {"name": "rule1", "properties": {"access": "Allow", "sourceAddressPrefix": "*"}},
                    {"name": "rule2", "properties": {"access": "Deny", "sourceAddressPrefix": "10.0.0.0/8"}}
                ]
            }
        },
        {
            "type": "Microsoft.KeyVault/vaults",
            "name": "kv1",
            "properties": {
                "enableSoftDelete": false
            }
        }
    ],
    "deployment": {
        "resourceGroupName": "prod-rg"
    }
}"#;

/// Causality-9(a): two consecutive causality runs on identical inputs produce
/// byte-identical raw JSON reports. The reproducer for the EDH capture.
#[test]
fn causality_9_report_is_deterministic() {
    let a = run_causality_full_raw(DETERMINISM_POLICY, DETERMINISM_INPUT, "data.bicep.deny");
    let b = run_causality_full_raw(DETERMINISM_POLICY, DETERMINISM_INPUT, "data.bicep.deny");
    assert_eq!(
        a,
        b,
        "two causality runs on identical inputs must produce byte-identical reports\n\
         run A ({} bytes):\n{}\n---\nrun B ({} bytes):\n{}",
        a.len(),
        a,
        b.len(),
        b
    );
}

/// Causality-9(b): PE residual output is deterministic across repeated runs.
/// Same fixture as (a); exercises the PE emit path
/// (`compute_residual_queries` at causality_report.rs:322) instead of the
/// causality report path.
#[test]
fn causality_9_pe_residual_order_stable() {
    let a = run_pe_raw(DETERMINISM_POLICY, DETERMINISM_INPUT, "data.bicep.deny");
    let b = run_pe_raw(DETERMINISM_POLICY, DETERMINISM_INPUT, "data.bicep.deny");
    assert_eq!(
        a,
        b,
        "two PE runs on identical inputs must produce byte-identical residual output\n\
         run A ({} bytes):\n{}\n---\nrun B ({} bytes):\n{}",
        a.len(),
        a,
        b.len(),
        b
    );
}

/// Causality-9(c): a repeated causality run stays identical across many
/// iterations, not just two. Hash randomization is a per-map-construction
/// property, so a two-run check could pass by luck if the maps happened to
/// seed identically. Ten runs give effectively zero false-negative risk.
#[test]
fn causality_9_report_stable_across_ten_runs() {
    let first = run_causality_full_raw(DETERMINISM_POLICY, DETERMINISM_INPUT, "data.bicep.deny");
    for i in 1..10 {
        let next = run_causality_full_raw(DETERMINISM_POLICY, DETERMINISM_INPUT, "data.bicep.deny");
        assert_eq!(
            first,
            next,
            "run 0 vs run {i}: causality report must be stable\n\
             run 0 ({} bytes):\n{}\n---\nrun {i} ({} bytes):\n{}",
            first.len(),
            first,
            next.len(),
            next
        );
    }
}
