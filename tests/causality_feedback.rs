// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Regression tests for the causality / partial-eval feedback items
//! filed against the `causality` branch.  Each test corresponds to a
//! numbered item in the feedback and asserts that the issue no longer
//! reproduces.

#![cfg(all(feature = "rvm", feature = "explanations"))]

use regorus::*;

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
    assert_eq!(cond.get("kind").and_then(|v| v.as_str()), Some("builtin"));
    assert_eq!(
        cond.get("builtin_name").and_then(|v| v.as_str()),
        Some(expected_builtin_name)
    );
    let left_provenance = cond
        .get("left")
        .and_then(|left| left.get("provenance"))
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert!(
        left_provenance.starts_with("input.resources")
            && left_provenance.contains(expected_subject_provenance_contains),
        "unexpected subject provenance for {expected_builtin_name}: {cond:#?}"
    );
    assert_eq!(
        cond.get("right").and_then(|right| right.get("value")),
        Some(&expected_right_value)
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

    assert_eq!(
        cond.get("kind").and_then(|v| v.as_str()),
        Some("comparison"),
        "not <comparison> should retain comparison kind; got: {cond:#?}"
    );
    assert_eq!(cond.get("negated").and_then(|v| v.as_bool()), Some(true));
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

    assert_eq!(
        cond.get("kind").and_then(|v| v.as_str()),
        Some("builtin"),
        "not <builtin> should retain builtin kind; got: {cond:#?}"
    );
    assert_eq!(cond.get("negated").and_then(|v| v.as_bool()), Some(true));

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
// Causality-5(a): builtin guards carry structured operands.
// ===========================================================================

#[test]
fn causality_5a_startswith_carries_structured_operands() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    lower(resource.name) == "premiumsa"
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

    for needle in ["resource.type ==", "lower(resource.name) =="] {
        let condition = find_condition(&report, needle)
            .unwrap_or_else(|| panic!("missing negative control '{needle}': {report:#?}"));
        assert_eq!(condition["kind"], "comparison");
        assert!(
            condition.get("builtin_name").is_none(),
            "non-guard builtin/comparison must not become a builtin condition: {condition:#?}"
        );
    }

    let report = run_causality_full(
        r#"
package bicep
import rego.v1

result := startswith("x", input.a)
result := false if {
    input.b == "y"
}
"#,
        r#"{"a":"q","b":"y","secret":"s3cr3t"}"#,
        "data.bicep.result",
    );
    let condition = find_condition(&report, "input.b ==")
        .unwrap_or_else(|| panic!("missing cross-definition negative control: {report:#?}"));
    assert_eq!(condition["kind"], "comparison");
    assert!(condition.get("builtin_name").is_none());
    assert!(
        condition["left"]["provenance"]
            .as_str()
            .is_some_and(|path| path.contains("input.b")),
        "comparison picked up stale builtin operands: {condition:#?}"
    );

    let report = run_causality_full(
        r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    startswith(resource.name, "prod-", false)
    msg := resource.name
}
"#,
        r#"{"resources":[{"name":"dev-svc"}]}"#,
        "data.bicep.deny",
    );
    let condition = find_condition(&report, "startswith(resource.name")
        .unwrap_or_else(|| panic!("missing output-argument negative control: {report:#?}"));
    assert_ne!(condition["kind"], "builtin");
    assert!(condition.get("builtin_name").is_none());
}

#[test]
fn causality_5a_pe_residual_carries_builtin_operator_and_value() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    startswith(input.deployment.resourceGroupName, "prod-")
    msg := sprintf("Resource '%s' in prod group", [resource.name])
}
"#;
    let input = r#"{"resources": [{ "name": "sa1" }]}"#;

    let result = run_pe(policy, input, "data.bicep.deny");
    let condition = result["residual_queries"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|query| query.as_array().unwrap())
        .find(|condition| condition["operator"] == "startswith")
        .unwrap_or_else(|| panic!("missing structured builtin residual: {result:#?}"));
    assert_eq!(condition["value"], "prod-");
    assert_eq!(
        condition["input_path"],
        "input.deployment.resourceGroupName"
    );
}

#[test]
fn causality_5a_negated_builtin_still_carries_operands() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    not startswith(resource.name, "test-")
    msg := sprintf("Resource '%s' must start with test-", [resource.name])
}
"#;
    let input = r#"{"resources": [{ "name": "prodResource1" }]}"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let condition = find_condition(&report, "not startswith(resource.name")
        .unwrap_or_else(|| panic!("missing negated builtin condition: {report:#?}"));
    assert_eq!(condition["kind"], "builtin");
    assert_eq!(condition["negated"], true);
    assert_eq!(condition["builtin_name"], "startswith");
    assert!(
        condition["left"]["provenance"]
            .as_str()
            .is_some_and(|path| path.contains("name")),
        "missing subject provenance: {condition:#?}"
    );
    assert_eq!(condition["right"]["value"], "test-");
}

#[test]
fn causality_5a_regex_match_carries_reversed_operands() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    regex.match("^prod-", resource.name)
    msg := sprintf("Resource '%s' uses prod prefix", [resource.name])
}
"#;
    let input = r#"{"resources": [{ "name": "prod-svc1" }]}"#;
    let report = run_causality_full(policy, input, "data.bicep.deny");
    assert_builtin_condition_shape(
        &report,
        "regex.match",
        "regex.match",
        "name",
        serde_json::json!("^prod-"),
    );
}

#[test]
fn causality_5a_endswith_covered() {
    let policy = r#"
package bicep
import rego.v1
deny contains msg if {
    some resource in input.resources
    endswith(resource.name, "-prod")
    msg := resource.name
}
"#;
    let report = run_causality_full(
        policy,
        r#"{"resources": [{ "name": "svc-prod" }]}"#,
        "data.bicep.deny",
    );
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
    let policy = r#"
package bicep
import rego.v1
deny contains msg if {
    some resource in input.resources
    contains(resource.name, "prod")
    msg := resource.name
}
"#;
    let report = run_causality_full(
        policy,
        r#"{"resources": [{ "name": "sa-prod-eastus" }]}"#,
        "data.bicep.deny",
    );
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
    let policy = r#"
package bicep
import rego.v1
deny contains msg if {
    some resource in input.resources
    strings.any_prefix_match(resource.name, ["prod-", "prd-"])
    msg := resource.name
}
"#;
    let report = run_causality_full(
        policy,
        r#"{"resources": [{ "name": "prod-svc1" }]}"#,
        "data.bicep.deny",
    );
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
    msg := resource.name
}
"#;
    let report = run_causality_full(
        policy,
        r#"{"resources": [{ "name": "svc1-prod" }]}"#,
        "data.bicep.deny",
    );
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
    let policy = r#"
package bicep
import rego.v1
deny contains msg if {
    some resource in input.resources
    net.cidr_contains("10.0.0.0/8", resource.properties.ipAddress)
    msg := resource.name
}
"#;
    let input = r#"{
        "resources": [{
            "name": "vm1",
            "properties": { "ipAddress": "10.1.2.3" }
        }]
    }"#;
    let report = run_causality_full(policy, input, "data.bicep.deny");
    assert_builtin_condition_shape(
        &report,
        "net.cidr_contains",
        "net.cidr_contains",
        "ipAddress",
        serde_json::json!("10.0.0.0/8"),
    );
}

// ===========================================================================
// Causality-5(b): negation is orthogonal to condition kind.
// ===========================================================================

#[test]
fn causality_5b_negated_comparison_full_shape() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    not resource.properties.minimumTlsVersion == "TLS1_0"
    msg := resource.name
}
"#;
    let input = r#"{
        "resources": [{
            "name": "stg1",
            "properties": { "minimumTlsVersion": "TLS1_2" }
        }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let condition = find_condition(&report, "not resource.properties.minimumTlsVersion")
        .unwrap_or_else(|| panic!("missing negated comparison: {report:#?}"));
    assert_eq!(condition["kind"], "comparison");
    assert_eq!(condition["negated"], true);
    assert_eq!(condition["operator"], "==");
    assert!(condition["left"]["provenance"]
        .as_str()
        .is_some_and(|path| path.contains("minimumTlsVersion")));
    assert_eq!(condition["right"]["value"], "TLS1_0");
}

#[test]
fn causality_5b_opaque_negation_emits_truthiness() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    not is_string(resource.name)
    msg := "resource.name must be a string"
}
"#;
    let report = run_causality_full(
        policy,
        r#"{"resources": [{ "name": 42 }]}"#,
        "data.bicep.deny",
    );
    let condition = find_condition(&report, "not is_string(resource.name")
        .unwrap_or_else(|| panic!("missing opaque negation: {report:#?}"));
    assert_eq!(condition["kind"], "truthiness");
    assert_eq!(condition["negated"], true);
    assert!(
        all_conditions(&report)
            .iter()
            .filter(|candidate| *candidate != &condition)
            .all(|candidate| candidate.get("negated").is_none()),
        "negation leaked to unrelated conditions: {report:#?}"
    );

    let report = run_causality_full(
        r#"
package bicep
import rego.v1

deny contains "input" if {
    not input.disabled
}

deny contains "literal" if {
    not false
}
"#,
        r#"{"disabled":false}"#,
        "data.bicep.deny",
    );
    for needle in ["not input.disabled", "not false"] {
        let condition = find_condition(&report, needle)
            .unwrap_or_else(|| panic!("missing truthiness negation '{needle}': {report:#?}"));
        assert_eq!(condition["kind"], "truthiness");
        assert_eq!(condition["negated"], true);
    }
}

#[test]
fn causality_5b_positive_omits_negated_key() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    msg := resource.name
}
"#;
    let report = run_causality_full(
        policy,
        r#"{"resources": [{"type":"Microsoft.Storage/storageAccounts","name":"stg1"}]}"#,
        "data.bicep.deny",
    );
    let condition = find_condition(&report, "resource.type ==")
        .unwrap_or_else(|| panic!("missing positive comparison: {report:#?}"));
    assert_eq!(condition["kind"], "comparison");
    assert!(condition.get("negated").is_none());
}

// ===========================================================================
// Causality-9: engine report emission is deterministic.
// ===========================================================================

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

const PE_DETERMINISM_POLICY: &str = r#"
package bicep
import rego.v1

deny contains msg if {
    input.deployment.status == "public"
    input.deployment.department == input.request.department
    msg := "public deployment"
}

deny contains msg if {
    input.deployment.owner == input.request.user
    msg := "owned deployment"
}
"#;

const PE_DETERMINISM_INPUT: &str = r#"{
    "request": {
        "department": "engineering",
        "user": "alice"
    }
}"#;

fn assert_nontrivial_residuals(raw: &str) {
    let result: serde_json::Value = serde_json::from_str(raw).unwrap();
    let queries = result["residual_queries"]
        .as_array()
        .unwrap_or_else(|| panic!("missing residual_queries; got: {result:#?}"));
    assert!(
        queries.len() >= 2,
        "expected at least two residual disjuncts; got: {result:#?}"
    );
    let max_condition_count = queries
        .iter()
        .map(|query| query.as_array().map_or(0, Vec::len))
        .max()
        .unwrap_or(0);
    assert!(
        max_condition_count >= 2,
        "expected a residual disjunct with at least two conditions; got: {result:#?}"
    );
}

#[test]
fn causality_9_report_is_deterministic() {
    let first = run_causality_full_raw(DETERMINISM_POLICY, DETERMINISM_INPUT, "data.bicep.deny");
    let second = run_causality_full_raw(DETERMINISM_POLICY, DETERMINISM_INPUT, "data.bicep.deny");
    assert_eq!(
        first, second,
        "two causality runs on identical inputs must produce byte-identical reports"
    );

    let changed_input = DETERMINISM_INPUT.replace("\"prod-rg\"", "\"dev-rg\"");
    let changed = run_causality_full_raw(DETERMINISM_POLICY, &changed_input, "data.bicep.deny");
    assert_ne!(
        first, changed,
        "the determinism comparison must remain sensitive to a genuinely different report"
    );
}

#[test]
fn causality_9_pe_residual_order_stable() {
    let first = run_pe_raw(
        PE_DETERMINISM_POLICY,
        PE_DETERMINISM_INPUT,
        "data.bicep.deny",
    );
    let second = run_pe_raw(
        PE_DETERMINISM_POLICY,
        PE_DETERMINISM_INPUT,
        "data.bicep.deny",
    );
    assert_nontrivial_residuals(&first);
    assert_eq!(
        first, second,
        "two PE runs on identical inputs must produce byte-identical residual output"
    );

    let changed_input = PE_DETERMINISM_INPUT.replace("\"alice\"", "\"bob\"");
    let changed = run_pe_raw(PE_DETERMINISM_POLICY, &changed_input, "data.bicep.deny");
    assert_nontrivial_residuals(&changed);
    assert_ne!(
        first, changed,
        "the PE determinism comparison must remain sensitive to a genuinely different residual"
    );
}

#[test]
fn causality_9_report_stable_across_ten_runs() {
    let first = run_causality_full_raw(DETERMINISM_POLICY, DETERMINISM_INPUT, "data.bicep.deny");
    for run in 1..10 {
        let next = run_causality_full_raw(DETERMINISM_POLICY, DETERMINISM_INPUT, "data.bicep.deny");
        assert_eq!(
            first, next,
            "causality report changed between run 0 and run {run}"
        );
    }
}
