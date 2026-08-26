// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(all(feature = "azure_policy", feature = "explanations", feature = "rvm"))]

//! Causality reporting for Azure-Policy-compiled programs.
//!
//! An AP definition compiles to a flat `main` entry point with no `CallRule`,
//! so no rule outcome is ever recorded. These tests pin the *content* of the
//! explanation, not merely that a report is produced — an empty report is the
//! exact failure mode this path had before, and asserting "a report exists"
//! would pass while the bug remained.

use regorus::languages::azure_policy::{compiler, parser};
use regorus::rvm::RegoVM;
use regorus::{Source, Value};

const POLICY: &str = r#"{
  "displayName": "Resources must be in eastus",
  "policyRule": {
    "if": {
      "field": "location",
      "notEquals": "eastus"
    },
    "then": {
      "effect": "deny"
    }
  }
}"#;

/// Compile `POLICY`, evaluate `resource`, and return the parsed causality report.
fn run(resource_json: &str) -> serde_json::Value {
    let source = Source::from_contents("policy.json".to_string(), POLICY.to_string()).unwrap();
    let defn = parser::parse_policy_definition(&source).unwrap();
    let program = compiler::compile_policy_definition(&defn).unwrap();

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
    vm.set_explanation_settings(regorus::evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode: regorus::evaluation_trace::ValueMode::Full,
        condition_mode: regorus::evaluation_trace::ConditionMode::AllContributing,
        detail: regorus::evaluation_trace::ExplanationDetail::Full,
        ..Default::default()
    });

    let result = vm.execute_entry_point_by_name("main").unwrap();
    let report = vm.take_causality_report(result).unwrap();
    serde_json::from_str(&report.to_string()).unwrap()
}

#[test]
fn ap_causality_names_the_policy_and_the_failing_condition() {
    let report = run(r#"{"location": "westus"}"#);

    let rules = report["rules"].as_array().expect("rules array");
    assert_eq!(
        rules.len(),
        1,
        "a rule-less AP program must still surface one synthetic rule, got: {report}"
    );
    assert_eq!(
        rules[0]["name"], "Resources must be in eastus",
        "rule should be named from the policy displayName, got: {report}"
    );

    let conditions = rules[0]["definitions"][0]["conditions"]
        .as_array()
        .expect("conditions array");
    assert_eq!(conditions.len(), 1, "expected one condition, got: {report}");
    let c = &conditions[0];

    // The author's own operator must survive, not just the Rego equivalent.
    assert_eq!(c["builtin_name"], "notEquals", "got: {report}");
    assert_eq!(c["operator"], "!=", "got: {report}");
    assert_eq!(c["kind"], "comparison", "got: {report}");

    // Actual and expected values are the point of the report.
    assert_eq!(c["left"]["value"], "westus", "actual value, got: {report}");
    assert_eq!(
        c["right"]["value"], "eastus",
        "expected value, got: {report}"
    );

    assert!(
        c["left"]["provenance"]
            .as_str()
            .is_some_and(|p| p.contains("location")),
        "actual operand should carry input provenance, got: {report}"
    );
}

#[test]
fn ap_causality_locates_the_condition_in_the_policy_json() {
    let report = run(r#"{"location": "westus"}"#);
    let c = &report["rules"][0]["definitions"][0]["conditions"][0];

    assert_eq!(
        c["location"]["row"], 6,
        "condition should point at the `notEquals` line of the policy JSON, got: {report}"
    );
    assert!(
        c["text"].as_str().is_some_and(|t| t.contains("notEquals")),
        "condition text should come from the policy source line, got: {report}"
    );
}

/// Negative control: the synthetic-rule fallback must not invent a rule when
/// no condition was recorded. Guards against the fallback firing on programs
/// it was not meant for.
#[test]
fn ap_causality_reports_success_when_the_policy_does_not_match() {
    let report = run(r#"{"location": "eastus"}"#);
    let c = &report["rules"][0]["definitions"][0]["conditions"][0];

    assert_eq!(
        c["outcome"], "failure",
        "notEquals against a matching value must not hold, got: {report}"
    );
    assert_eq!(c["left"]["value"], "eastus", "got: {report}");
}

// ── Step 6: source_alias on aliased conditions ──────────────────────────────
//
// These pin the FQ alias name added to `left`/`right` operands, which lets a
// consumer map straight to the alias's ARM `defaultPath` instead of inverting
// the (lower-cased, `properties`-flattened) `provenance` path. Each test pins
// the actual JSON field, not merely that the report is non-empty — matching
// this file's existing convention (see the module doc comment above).

use regorus::languages::azure_policy::aliases::AliasRegistry;
use std::sync::Arc;

const SCALAR_ALIAS_JSON: &str = r#"[{
    "namespace": "Microsoft.Storage",
    "resourceTypes": [{
        "resourceType": "storageAccounts",
        "aliases": [{
            "name": "Microsoft.Storage/storageAccounts/accessTier",
            "defaultPath": "properties.accessTier",
            "paths": []
        }]
    }]
}]"#;

const SCALAR_ALIAS_POLICY: &str = r#"{
  "displayName": "Hot tier is denied",
  "policyRule": {
    "if": {
      "allOf": [
        { "field": "type", "equals": "Microsoft.Storage/storageAccounts" },
        { "field": "Microsoft.Storage/storageAccounts/accessTier", "equals": "Hot" }
      ]
    },
    "then": { "effect": "deny" }
  }
}"#;

const ARRAY_ALIAS_JSON: &str = r#"[{
    "namespace": "Microsoft.Storage",
    "resourceTypes": [{
        "resourceType": "storageAccounts",
        "aliases": [{
            "name": "Microsoft.Storage/storageAccounts/networkAcls.ipRules[*].value",
            "defaultPath": "properties.networkAcls.ipRules[*].value",
            "paths": []
        }]
    }]
}]"#;

const ARRAY_ALIAS_POLICY: &str = r#"{
  "displayName": "Blocked IP rule",
  "policyRule": {
    "if": {
      "allOf": [
        { "field": "type", "equals": "Microsoft.Storage/storageAccounts" },
        { "field": "Microsoft.Storage/storageAccounts/networkAcls.ipRules[*].value", "equals": "10.0.0.1" }
      ]
    },
    "then": { "effect": "deny" }
  }
}"#;

/// Compile `policy_json` with `alias_json` loaded, normalize `resource_json`
/// through the real alias registry (not a hand-built envelope, so the input
/// is genuinely alias-shaped like production), evaluate, and return the
/// parsed causality report.
fn run_with_aliases(alias_json: &str, policy_json: &str, resource_json: &str) -> serde_json::Value {
    let mut registry = AliasRegistry::new();
    registry.load_from_json(alias_json).unwrap();
    let registry = Arc::new(registry);

    let source = Source::from_contents("policy.json".to_string(), policy_json.to_string()).unwrap();
    let defn = parser::parse_policy_definition(&source).unwrap();
    let program =
        compiler::compile_policy_definition_with_aliases(&defn, Arc::clone(&registry)).unwrap();

    let arm_resource = Value::from_json_str(resource_json).unwrap();
    let input = registry.normalize_and_wrap(&arm_resource, None, None, Some(Value::new_object()));

    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_input(input);
    vm.set_explanation_settings(regorus::evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode: regorus::evaluation_trace::ValueMode::Full,
        condition_mode: regorus::evaluation_trace::ConditionMode::AllContributing,
        detail: regorus::evaluation_trace::ExplanationDetail::Full,
        ..Default::default()
    });

    let result = vm.execute_entry_point_by_name("main").unwrap();
    let report = vm.take_causality_report(result).unwrap();
    serde_json::from_str(&report.to_string()).unwrap()
}

/// Finds the condition whose `left.provenance` contains `needle`, so tests
/// don't depend on selector conditions (`type == ...`) staying in a fixed
/// position within `conditions[]`.
fn find_condition<'a>(report: &'a serde_json::Value, needle: &str) -> &'a serde_json::Value {
    report["rules"][0]["definitions"][0]["conditions"]
        .as_array()
        .expect("conditions array")
        .iter()
        .find(|c| {
            c["left"]["provenance"]
                .as_str()
                .is_some_and(|p| p.contains(needle))
        })
        .unwrap_or_else(|| {
            panic!("no condition with provenance containing '{needle}', got: {report}")
        })
}

#[test]
fn source_alias_on_a_plain_property_condition() {
    let report = run_with_aliases(
        SCALAR_ALIAS_JSON,
        SCALAR_ALIAS_POLICY,
        r#"{"type": "Microsoft.Storage/storageAccounts", "properties": {"accessTier": "Hot"}}"#,
    );
    let c = find_condition(&report, "accesstier");

    assert_eq!(
        c["left"]["source_alias"], "Microsoft.Storage/storageAccounts/accessTier",
        "the plain scalar alias case must report the FQ alias name, got: {report}"
    );
}

#[test]
fn source_alias_on_a_wildcard_condition() {
    let report = run_with_aliases(
        ARRAY_ALIAS_JSON,
        ARRAY_ALIAS_POLICY,
        r#"{"type": "Microsoft.Storage/storageAccounts", "properties": {"networkAcls": {"ipRules": [{"value": "10.0.0.1"}]}}}"#,
    );
    let c = find_condition(&report, "networkacls.iprules");

    assert_eq!(
        c["left"]["source_alias"], "Microsoft.Storage/storageAccounts/networkAcls.ipRules[*].value",
        "the per-element wildcard-condition case must carry the same FQ alias name as the plain case, got: {report}"
    );
}

#[test]
fn source_alias_is_absent_for_a_non_aliased_condition() {
    // Negative control: a raw `type` selector never goes through alias
    // resolution, so it must not carry a source_alias -- proves the field is
    // populated selectively rather than defaulted to something that would
    // mask an unpopulated case as attributed.
    let report = run_with_aliases(
        SCALAR_ALIAS_JSON,
        SCALAR_ALIAS_POLICY,
        r#"{"type": "Microsoft.Storage/storageAccounts", "properties": {"accessTier": "Hot"}}"#,
    );
    let type_condition = report["rules"][0]["definitions"][0]["conditions"]
        .as_array()
        .expect("conditions array")
        .iter()
        .find(|c| c["left"]["provenance"].as_str() == Some("input.resource.type"))
        .expect("expected a condition on the type selector");

    assert!(
        type_condition["left"].get("source_alias").is_none(),
        "a raw (non-aliased) field must not carry source_alias, got: {report}"
    );
}
