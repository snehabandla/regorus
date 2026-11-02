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

fn run_rg1_case(
    policy: &str,
    input: &str,
    settings: evaluation_trace::ExplanationSettings,
) -> (Value, serde_json::Value) {
    let mut engine = Engine::new();
    engine.add_policy("rg1.rego".into(), policy.into()).unwrap();
    let input = Value::from_json_str(input).unwrap();
    engine.set_input(input.clone());
    let interpreted = engine.eval_rule("data.bicep.deny".into()).unwrap();
    let compiled = engine
        .compile_with_entrypoint(&Rc::from("data.bicep.deny"))
        .unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &["data.bicep.deny"])
            .unwrap();

    let mut plain = rvm::RegoVM::new_with_policy(compiled.clone());
    plain.load_program(program.clone());
    plain.set_input(input.clone());
    let plain_result = plain
        .execute_entry_point_by_name("data.bicep.deny")
        .unwrap();
    assert_eq!(plain_result, interpreted);

    let mut traced = rvm::RegoVM::new_with_policy(compiled);
    traced.load_program(program);
    traced.set_explanation_settings(settings);
    traced.set_input(input);
    let result = traced
        .execute_entry_point_by_name("data.bicep.deny")
        .unwrap();
    assert_eq!(result, plain_result);
    let report = traced.take_causality_report(result.clone()).unwrap();
    (result, serde_json::from_str(&report).unwrap())
}

#[test]
fn rg1_negated_reference_reports_concrete_path_and_absence() {
    use evaluation_trace::{ConditionMode, ExplanationDetail, ExplanationSettings, ValueMode};

    let policy = r#"
package bicep
import rego.v1
deny contains "missing or false" if {
    some r in input.resources
    not r.properties.enabled
}
"#;
    for condition_mode in [ConditionMode::PrimaryOnly, ConditionMode::AllContributing] {
        for detail in [ExplanationDetail::Standard, ExplanationDetail::Full] {
            for value_mode in [ValueMode::Full, ValueMode::Redacted] {
                for (resource, matches, absent) in [
                    (r#"{"properties":{}}"#, true, true),
                    (r#"{}"#, true, true),
                    (r#"{"properties":{"enabled":false}}"#, true, false),
                    (r#"{"properties":{"enabled":true}}"#, false, false),
                    (r#"{"properties":{"enabled":null}}"#, false, false),
                    (r#"{"properties":{"enabled":0}}"#, false, false),
                    (r#"{"properties":{"enabled":""}}"#, false, false),
                    (r#"{"properties":{"enabled":[]}}"#, false, false),
                    (r#"{"properties":{"enabled":{}}}"#, false, false),
                ] {
                    let input = format!(r#"{{"resources":{{"app":{resource}}}}}"#);
                    let (result, report) = run_rg1_case(
                        policy,
                        &input,
                        ExplanationSettings {
                            enabled: true,
                            condition_mode,
                            detail,
                            value_mode,
                            ..Default::default()
                        },
                    );
                    let values = result.as_set().unwrap();
                    assert_eq!(values.len(), usize::from(matches), "{input}: {report:#}");
                    if !matches {
                        assert!(report["rules"][0].get("emissions").is_none(), "{report:#}");
                        continue;
                    }
                    let emissions = report["rules"][0]["emissions"].as_array().unwrap();
                    assert_eq!(emissions.len(), 1, "{report:#}");
                    assert!(values.contains(&Value::from("missing or false")));
                    let conditions = emissions[0]["conditions"].as_array().unwrap();
                    let condition = conditions
                        .iter()
                        .find(|c| c["text"] == "not r.properties.enabled")
                        .unwrap();
                    assert_eq!(condition["kind"], "truthiness");
                    assert_eq!(condition["negated"], true);
                    assert_eq!(condition["outcome"], "success");
                    assert_eq!(condition["left"]["value"], true);
                    assert_eq!(
                        condition["left"]["provenance"], "input.resources.app.properties.enabled",
                        "{condition:#}"
                    );
                    assert_eq!(
                        condition["left"].get("absent"),
                        absent.then_some(&serde_json::Value::Bool(true))
                    );
                    assert!(condition.get("right").is_none(), "{condition:#}");
                }
            }
        }
    }
}

#[test]
fn rg1_nested_reference_keeps_each_emissions_array_index() {
    let policy = r#"
package bicep
import rego.v1
deny contains child.name if {
    some r in input.resources
    some child in r.properties.children
    not child.enabled
}
"#;
    let input = r#"{"resources":{"app":{"properties":{"children":[
        {"name":"valid","enabled":true},
        {"name":"missing"},
        {"name":"false","enabled":false}
    ]}}}}"#;
    let (result, report) = run_rg1_case(
        policy,
        input,
        evaluation_trace::ExplanationSettings {
            enabled: true,
            detail: evaluation_trace::ExplanationDetail::Full,
            ..Default::default()
        },
    );
    let values = result.as_set().unwrap();
    assert_eq!(values.len(), 2);
    assert!(values.contains(&Value::from("missing")));
    assert!(values.contains(&Value::from("false")));
    let emissions = report["rules"][0]["emissions"].as_array().unwrap();
    assert_eq!(emissions.len(), 2);
    for (name, index, absent) in [("missing", 1, true), ("false", 2, false)] {
        let emission = emissions.iter().find(|e| e["result"] == name).unwrap();
        let condition = emission["conditions"]
            .as_array()
            .unwrap()
            .iter()
            .find(|c| c["text"] == "not child.enabled")
            .unwrap();
        assert_eq!(
            condition["left"]["provenance"],
            format!("input.resources.app.properties.children[{index}].enabled"),
            "{condition:#}"
        );
        assert_eq!(
            condition["left"].get("absent"),
            absent.then_some(&serde_json::Value::Bool(true))
        );
    }
}

#[test]
fn rg1_direct_and_dynamic_references_preserve_redaction() {
    use evaluation_trace::{ExplanationDetail, ExplanationSettings, ValueMode};

    for (expression, input, path, absent) in [
        ("not input.enabled", r#"{}"#, "input.enabled", true),
        (
            "not input.enabled",
            r#"{"enabled":false}"#,
            "input.enabled",
            false,
        ),
        (
            "key := \"enabled\"\nnot input.properties[key]",
            r#"{"properties":{}}"#,
            "input.properties.enabled",
            true,
        ),
        (
            "key := input.key\nnot input.properties[key]",
            r#"{"key":"enabled"}"#,
            "input.properties.enabled",
            true,
        ),
        (
            "key := input.key\nnot input.properties[key]",
            r#"{"key":"password"}"#,
            "input.properties.password",
            true,
        ),
        (
            "not input.resources[0].enabled",
            r#"{}"#,
            "input.resources[0].enabled",
            true,
        ),
        (
            "i := input.i\nnot input.resources[i].enabled",
            r#"{"i":0}"#,
            "input.resources[0].enabled",
            true,
        ),
        ("not input.password", r#"{}"#, "input.password", true),
        (
            "not input.password",
            r#"{"password":false}"#,
            "input.password",
            false,
        ),
    ] {
        for value_mode in [ValueMode::Full, ValueMode::Redacted] {
            let policy = format!(
                "package bicep\nimport rego.v1\ndeny contains \"violation\" if {{\n{expression}\n}}"
            );
            let (result, report) = run_rg1_case(
                &policy,
                input,
                ExplanationSettings {
                    enabled: true,
                    detail: ExplanationDetail::Full,
                    value_mode,
                    ..Default::default()
                },
            );
            assert_eq!(result.as_set().unwrap().len(), 1);
            let condition = find_condition(&report, "not input.").unwrap();
            let redacted = value_mode == ValueMode::Redacted && path.ends_with(".password");
            assert_eq!(condition["left"]["provenance"], path, "{condition:#}");
            assert_eq!(condition["left"]["redacted"], redacted);
            assert_eq!(
                condition["left"]["value"],
                if redacted {
                    serde_json::json!("<redacted>")
                } else {
                    serde_json::json!(true)
                }
            );
            assert_eq!(
                condition["left"].get("absent"),
                absent.then_some(&serde_json::Value::Bool(true))
            );
        }
    }
}

#[test]
fn rg1_unknown_input_path_is_not_reported_absent() {
    let policy = r#"
package bicep
import rego.v1
deny contains "v" if {
    not input.context.enabled
}
"#;
    for (unknowns, absent) in [
        (vec!["input.context".to_string()], false),
        (vec!["input.other".to_string()], true),
    ] {
        let (result, report) = run_rg1_case(
            policy,
            r#"{}"#,
            evaluation_trace::ExplanationSettings {
                enabled: true,
                detail: evaluation_trace::ExplanationDetail::Full,
                assume_unknown_input: true,
                unknowns,
                ..Default::default()
            },
        );
        assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
        let condition = find_condition(&report, "not input.context.enabled").unwrap();
        assert_eq!(
            condition["left"]["provenance"], "input.context.enabled",
            "{condition:#}"
        );
        assert_eq!(
            condition["left"].get("absent"),
            absent.then_some(&serde_json::Value::Bool(true)),
            "{condition:#}"
        );
    }
}

#[test]
fn rg1_undefined_dynamic_key_does_not_fabricate_absent_path() {
    let policy = r#"
package bicep
import rego.v1
deny contains "v" if {
    not input[input.key]
}
"#;
    let (result, report) = run_rg1_case(
        policy,
        r#"{"<undefined>": true}"#,
        evaluation_trace::ExplanationSettings {
            enabled: true,
            detail: evaluation_trace::ExplanationDetail::Full,
            ..Default::default()
        },
    );
    assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
    let condition = find_condition(&report, "not input[input.key]").unwrap();
    assert!(
        condition["left"].get("absent").is_none(),
        "an unresolved key must not produce a concrete absent path: {condition:#}"
    );
    assert_ne!(
        condition["left"]["provenance"], "input[\"<undefined>\"]",
        "an unresolved key must not name a concrete input path: {condition:#}"
    );

    // Negative control: the literal key really exists, so the negation fails.
    let (control, _) = run_rg1_case(
        "package bicep\nimport rego.v1\ndeny contains \"v\" if {\n    not input[\"<undefined>\"]\n}\n",
        r#"{"<undefined>": true}"#,
        evaluation_trace::ExplanationSettings {
            enabled: true,
            ..Default::default()
        },
    );
    assert!(control.as_set().unwrap().is_empty());
}

/// Every condition in the report, from both per-emission and per-definition lists.
fn rg5_conditions<'a>(report: &'a serde_json::Value, text: &str) -> Vec<&'a serde_json::Value> {
    let mut out = Vec::new();
    for rule in report["rules"].as_array().into_iter().flatten() {
        for list in ["emissions", "definitions"] {
            for entry in rule[list].as_array().into_iter().flatten() {
                for cond in entry["conditions"].as_array().into_iter().flatten() {
                    if cond["text"] == text {
                        out.push(cond);
                    }
                }
            }
        }
    }
    out
}

/// Like `rg5_conditions`, but matches text that starts with `prefix`
/// (existence conditions append a `[matched: ...]` decoration).
fn rg5_conditions_prefix<'a>(
    report: &'a serde_json::Value,
    prefix: &str,
) -> Vec<&'a serde_json::Value> {
    let mut out = Vec::new();
    for rule in report["rules"].as_array().into_iter().flatten() {
        for list in ["emissions", "definitions"] {
            for entry in rule[list].as_array().into_iter().flatten() {
                for cond in entry["conditions"].as_array().into_iter().flatten() {
                    if cond["text"].as_str().is_some_and(|t| t.starts_with(prefix)) {
                        out.push(cond);
                    }
                }
            }
        }
    }
    out
}

/// Traced RVM only. Assumption mode intentionally changes results, so the
/// interpreter/plain parity in `run_rg1_case` does not apply.
fn rg5_traced_only(
    policy: &str,
    input: &str,
    settings: evaluation_trace::ExplanationSettings,
) -> serde_json::Value {
    let mut engine = Engine::new();
    engine.add_policy("rg5.rego".into(), policy.into()).unwrap();
    let compiled = engine
        .compile_with_entrypoint(&Rc::from("data.bicep.deny"))
        .unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &["data.bicep.deny"])
            .unwrap();
    let mut vm = rvm::RegoVM::new_with_policy(compiled);
    vm.load_program(program);
    vm.set_explanation_settings(settings);
    vm.set_input(Value::from_json_str(input).unwrap());
    let result = vm.execute_entry_point_by_name("data.bicep.deny").unwrap();
    serde_json::from_str(&vm.take_causality_report(result).unwrap()).unwrap()
}

fn rg5_settings(
    condition_mode: evaluation_trace::ConditionMode,
) -> evaluation_trace::ExplanationSettings {
    evaluation_trace::ExplanationSettings {
        enabled: true,
        condition_mode,
        detail: evaluation_trace::ExplanationDetail::Full,
        value_mode: evaluation_trace::ValueMode::Full,
        ..Default::default()
    }
}

fn rg5_assert_operand(
    cond: &serde_json::Value,
    side: &str,
    value: serde_json::Value,
    provenance: Option<&str>,
) {
    assert_eq!(cond[side]["value"], value, "{side}.value: {cond:#}");
    assert_eq!(
        cond[side].get("provenance").and_then(|p| p.as_str()),
        provenance,
        "{side}.provenance: {cond:#}"
    );
}

#[test]
fn rg5_positive_comparison_between_two_paths_reports_both_operands() {
    use evaluation_trace::ConditionMode;
    let input = r#"{"resources":{"sa":{"name":"sa1","sku":"Standard_LRS","kind":"StorageV2","used":1,"limit":5}}}"#;
    for (expr, op, left, left_path, right, right_path) in [
        (
            "r.sku != r.kind",
            "!=",
            serde_json::json!("Standard_LRS"),
            "input.resources.sa.sku",
            serde_json::json!("StorageV2"),
            "input.resources.sa.kind",
        ),
        (
            "r.used < r.limit",
            "<",
            serde_json::json!(1),
            "input.resources.sa.used",
            serde_json::json!(5),
            "input.resources.sa.limit",
        ),
    ] {
        let policy = format!(
            "package bicep\nimport rego.v1\ndeny contains r.name if {{\n    some r in input.resources\n    {expr}\n}}\n"
        );
        for mode in [ConditionMode::PrimaryOnly, ConditionMode::AllContributing] {
            let (result, report) = run_rg1_case(&policy, input, rg5_settings(mode));
            assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
            let conds = rg5_conditions(&report, expr);
            assert!(!conds.is_empty(), "missing `{expr}`: {report:#}");
            for cond in conds {
                assert_eq!(cond["kind"], "comparison");
                assert_eq!(cond["operator"], op);
                assert_eq!(cond["outcome"], "success");
                assert!(cond.get("negated").is_none());
                rg5_assert_operand(cond, "left", left.clone(), Some(left_path));
                rg5_assert_operand(cond, "right", right.clone(), Some(right_path));
            }
        }
    }
}

#[test]
fn rg5_literal_operand_keeps_source_order_without_provenance() {
    let input = r#"{"resources":{"sa":{"name":"sa1","kind":"StorageV2"}}}"#;
    for (expr, left, left_path, right, right_path) in [
        (
            "r.kind == \"StorageV2\"",
            "StorageV2",
            Some("input.resources.sa.kind"),
            "StorageV2",
            None,
        ),
        (
            "\"StorageV2\" == r.kind",
            "StorageV2",
            None,
            "StorageV2",
            Some("input.resources.sa.kind"),
        ),
    ] {
        let policy = format!(
            "package bicep\nimport rego.v1\ndeny contains r.name if {{\n    some r in input.resources\n    {expr}\n}}\n"
        );
        let (result, report) = run_rg1_case(
            &policy,
            input,
            rg5_settings(evaluation_trace::ConditionMode::PrimaryOnly),
        );
        assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
        let conds = rg5_conditions(&report, expr);
        assert!(!conds.is_empty(), "missing `{expr}`: {report:#}");
        for cond in conds {
            rg5_assert_operand(cond, "left", serde_json::json!(left), left_path);
            rg5_assert_operand(cond, "right", serde_json::json!(right), right_path);
        }
    }
}

#[test]
fn rg5_failed_and_undefined_comparisons_report_operands() {
    let policy = r#"
package bicep
import rego.v1
deny contains r.name if {
    some r in input.resources
    r.kind == "StorageV2"
    r.tier != r.sku
}
"#;
    let input = r#"{"resources":{
        "sa":{"name":"sa1","kind":"StorageV2","sku":"Standard_LRS"},
        "kv":{"name":"kv1","kind":"KeyVault"}
    }}"#;
    let (result, report) = run_rg1_case(
        policy,
        input,
        rg5_settings(evaluation_trace::ConditionMode::AllContributing),
    );
    assert!(result.as_set().unwrap().is_empty(), "{report:#}");

    let kind = rg5_conditions(&report, "r.kind == \"StorageV2\"");
    let failed = kind
        .iter()
        .find(|c| c["outcome"] == "failure")
        .unwrap_or_else(|| panic!("no failed kind comparison: {report:#}"));
    rg5_assert_operand(
        failed,
        "left",
        serde_json::json!("KeyVault"),
        Some("input.resources.kv.kind"),
    );
    rg5_assert_operand(failed, "right", serde_json::json!("StorageV2"), None);

    // `sa` reaches the second comparison with `tier` missing: the comparison is Undefined.
    let tier = rg5_conditions(&report, "r.tier != r.sku");
    let undefined = tier
        .iter()
        .find(|c| c["outcome"] == "failure")
        .unwrap_or_else(|| panic!("no failed tier comparison: {report:#}"));
    rg5_assert_operand(
        undefined,
        "left",
        serde_json::json!("<undefined>"),
        Some("input.resources.sa.tier"),
    );
    rg5_assert_operand(
        undefined,
        "right",
        serde_json::json!("Standard_LRS"),
        Some("input.resources.sa.sku"),
    );
}

#[test]
fn rg5_redacted_mode_redacts_sensitive_comparison_operand() {
    let policy = r#"
package bicep
import rego.v1
deny contains "weak" if {
    input.password != "Str0ng!"
}
"#;
    let (result, report) = run_rg1_case(
        policy,
        r#"{"password":"hunter2"}"#,
        evaluation_trace::ExplanationSettings {
            enabled: true,
            detail: evaluation_trace::ExplanationDetail::Full,
            value_mode: evaluation_trace::ValueMode::Redacted,
            ..Default::default()
        },
    );
    assert_eq!(result.as_set().unwrap().len(), 1);
    let conds = rg5_conditions(&report, "input.password != \"Str0ng!\"");
    assert!(!conds.is_empty(), "{report:#}");
    for cond in conds {
        assert_eq!(cond["left"]["value"], "<redacted>", "{cond:#}");
        assert_eq!(cond["left"]["redacted"], true);
        assert_eq!(cond["left"]["provenance"], "input.password");
        assert!(
            !cond.to_string().contains("hunter2"),
            "secret leaked: {cond:#}"
        );
    }
}

#[test]
fn rg5b_membership_reports_value_then_collection_for_both_polarities() {
    use evaluation_trace::ConditionMode;
    let input =
        r#"{"allowed":["westus","eastus"],"resources":{"sa":{"name":"sa1","location":"westus"}}}"#;
    for (expr, negated, matches) in [
        ("r.location in input.allowed", false, true),
        ("not r.location in input.allowed", true, false),
    ] {
        let policy = format!(
            "package bicep\nimport rego.v1\ndeny contains r.name if {{\n    some r in input.resources\n    {expr}\n}}\n"
        );
        for mode in [ConditionMode::PrimaryOnly, ConditionMode::AllContributing] {
            let (result, report) = run_rg1_case(&policy, input, rg5_settings(mode));
            assert_eq!(
                result.as_set().unwrap().len(),
                usize::from(matches),
                "{report:#}"
            );
            let conds = rg5_conditions(&report, expr);
            assert!(!conds.is_empty(), "missing `{expr}`: {report:#}");
            for cond in conds {
                assert_eq!(cond["operator"], "in", "{cond:#}");
                assert_eq!(
                    cond.get("negated")
                        .and_then(|v| v.as_bool())
                        .unwrap_or(false),
                    negated
                );
                rg5_assert_operand(
                    cond,
                    "left",
                    serde_json::json!("westus"),
                    Some("input.resources.sa.location"),
                );
                rg5_assert_operand(
                    cond,
                    "right",
                    serde_json::json!(["westus", "eastus"]),
                    Some("input.allowed"),
                );
            }
        }
    }
}

#[test]
fn rg5b_membership_with_literal_collection_has_no_collection_path() {
    let expr = "r.location in {\"westus\", \"eastus\"}";
    let policy = format!(
        "package bicep\nimport rego.v1\ndeny contains r.name if {{\n    some r in input.resources\n    {expr}\n}}\n"
    );
    let (result, report) = run_rg1_case(
        &policy,
        r#"{"resources":{"sa":{"name":"sa1","location":"westus"}}}"#,
        rg5_settings(evaluation_trace::ConditionMode::PrimaryOnly),
    );
    assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
    let conds = rg5_conditions(&report, expr);
    assert!(!conds.is_empty(), "{report:#}");
    for cond in conds {
        assert_eq!(cond["kind"], "comparison", "{cond:#}");
        assert_eq!(cond["operator"], "in", "{cond:#}");
        rg5_assert_operand(
            cond,
            "left",
            serde_json::json!("westus"),
            Some("input.resources.sa.location"),
        );
        assert!(
            cond["right"]["value"].is_array(),
            "set literal serializes as a collection: {cond:#}"
        );
        assert!(cond["right"].get("provenance").is_none(), "{cond:#}");
    }
}

#[test]
fn rg5_redaction_covers_other_operand_and_nested_secrets() {
    use evaluation_trace::{ExplanationDetail, ExplanationSettings, ValueMode};
    let redacted = ExplanationSettings {
        enabled: true,
        detail: ExplanationDetail::Full,
        value_mode: ValueMode::Redacted,
        condition_mode: evaluation_trace::ConditionMode::AllContributing,
        ..Default::default()
    };
    for (body, input, secret) in [
        // Sensitive left, harmless right that equals / contains the secret.
        (
            "input.api_key in input.valid",
            r#"{"api_key":"K1","valid":["K1","K2"]}"#,
            "K2",
        ),
        (
            "input.secret_token == input.expected",
            r#"{"secret_token":"T9","expected":"T9"}"#,
            "T9",
        ),
        // Harmless path whose value nests a secret.
        (
            "input.profile != {}",
            r#"{"profile":{"password":"hunter2","name":"alice"}}"#,
            "hunter2",
        ),
        (
            "input.items[0] != {}",
            r#"{"items":[{"name":"a","creds":[{"token":"tok123"}]}]}"#,
            "tok123",
        ),
    ] {
        let policy =
            format!("package bicep\nimport rego.v1\ndeny contains \"v\" if {{\n    {body}\n}}\n");
        let (result, report) = run_rg1_case(&policy, input, redacted.clone());
        assert_eq!(result.as_set().unwrap().len(), 1, "{body}: {report:#}");
        let conds = rg5_conditions(&report, body);
        assert!(!conds.is_empty(), "missing `{body}`: {report:#}");
        assert!(
            !report.to_string().contains(secret),
            "`{secret}` leaked for `{body}`: {report:#}"
        );
        for cond in conds {
            assert!(
                cond["left"]["redacted"] == true || cond["right"]["redacted"] == true,
                "a redacted operand should be marked: {cond:#}"
            );
        }
    }

    // Negative control: Full mode keeps every operand verbatim.
    let (_, full) = run_rg1_case(
        "package bicep\nimport rego.v1\ndeny contains \"v\" if {\n    input.profile != {}\n}\n",
        r#"{"profile":{"password":"hunter2","name":"alice"}}"#,
        rg5_settings(evaluation_trace::ConditionMode::PrimaryOnly),
    );
    assert!(full.to_string().contains("hunter2"), "{full:#}");
    // And a harmless comparison is not over-redacted.
    let (_, plain) = run_rg1_case(
        "package bicep\nimport rego.v1\ndeny contains \"v\" if {\n    input.profile.name != \"bob\"\n}\n",
        r#"{"profile":{"password":"hunter2","name":"alice"}}"#,
        redacted,
    );
    let cond = rg5_conditions(&plain, "input.profile.name != \"bob\"");
    assert!(!cond.is_empty(), "{plain:#}");
    assert_eq!(cond[0]["left"]["value"], "alice", "{plain:#}");
    assert_eq!(cond[0]["right"]["value"], "bob", "{plain:#}");
}

#[test]
fn rg5_existence_guard_on_comparison_result_keeps_boolean() {
    let body = "_ = (input.a != input.b)";
    let policy =
        format!("package bicep\nimport rego.v1\ndeny contains \"defined\" if {{\n    {body}\n}}\n");
    for (input, expected) in [(r#"{"a":1,"b":1}"#, false), (r#"{"a":1,"b":2}"#, true)] {
        let (result, report) = run_rg1_case(
            &policy,
            input,
            rg5_settings(evaluation_trace::ConditionMode::AllContributing),
        );
        assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
        let existence: Vec<_> = rg5_conditions_prefix(&report, body)
            .into_iter()
            .filter(|c| c["kind"] == "existence")
            .collect();
        assert!(
            !existence.is_empty(),
            "no existence guard for `{body}`: {report:#}"
        );
        for cond in existence {
            assert_eq!(cond["left"]["value"], expected, "{cond:#}");
            assert!(cond.get("right").is_none(), "{cond:#}");
        }
    }
}

#[test]
fn rg5_membership_against_object_and_assumed_operand() {
    // Object collection: `in` checks values; the collection is reported whole.
    let expr = "r.tier in input.tiers";
    let policy = format!(
        "package bicep\nimport rego.v1\ndeny contains r.name if {{\n    some r in input.resources\n    {expr}\n}}\n"
    );
    let (result, report) = run_rg1_case(
        &policy,
        r#"{"tiers":{"a":"gold","b":"silver"},"resources":{"sa":{"name":"sa1","tier":"gold"}}}"#,
        rg5_settings(evaluation_trace::ConditionMode::PrimaryOnly),
    );
    assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
    let conds = rg5_conditions(&report, expr);
    assert!(!conds.is_empty(), "{report:#}");
    for cond in conds {
        rg5_assert_operand(
            cond,
            "left",
            serde_json::json!("gold"),
            Some("input.resources.sa.tier"),
        );
        rg5_assert_operand(
            cond,
            "right",
            serde_json::json!({"a":"gold","b":"silver"}),
            Some("input.tiers"),
        );
    }

    // Assumed comparison: an unknown operand stays Undefined, with the outcome assumed.
    let body = "input.context.region != \"westus\"";
    let assumed = rg5_traced_only(
        &format!("package bicep\nimport rego.v1\ndeny contains \"v\" if {{\n    {body}\n}}\n"),
        r#"{}"#,
        evaluation_trace::ExplanationSettings {
            enabled: true,
            detail: evaluation_trace::ExplanationDetail::Full,
            value_mode: evaluation_trace::ValueMode::Full,
            assume_unknown_input: true,
            unknowns: vec!["input.context".to_string()],
            ..Default::default()
        },
    );
    let conds = rg5_conditions(&assumed, body);
    assert!(!conds.is_empty(), "{assumed:#}");
    for cond in conds {
        assert_eq!(cond["outcome"], "assumed", "{cond:#}");
        rg5_assert_operand(
            cond,
            "left",
            serde_json::json!("<undefined>"),
            Some("input.context.region"),
        );
        rg5_assert_operand(cond, "right", serde_json::json!("westus"), None);
    }
}

#[test]
fn rg5_large_collection_operand_is_truncated_with_length() {
    let expr = "r.x in input.huge";
    let policy = format!(
        "package bicep\nimport rego.v1\ndeny contains r.id if {{\n    some r in input.resources\n    {expr}\n}}\n"
    );
    let huge: Vec<u32> = (0..1000).collect();
    let input = serde_json::json!({
        "huge": huge,
        "resources": {"a": {"id": "a", "x": 0}, "b": {"id": "b", "x": 999}}
    })
    .to_string();
    for mode in [
        evaluation_trace::ValueMode::Full,
        evaluation_trace::ValueMode::Redacted,
    ] {
        let (result, report) = run_rg1_case(
            &policy,
            &input,
            evaluation_trace::ExplanationSettings {
                enabled: true,
                detail: evaluation_trace::ExplanationDetail::Full,
                value_mode: mode,
                ..Default::default()
            },
        );
        // Evaluation is unaffected: 999 is beyond the reported prefix but still matches.
        assert_eq!(result.as_set().unwrap().len(), 2, "{report:#}");
        let conds = rg5_conditions(&report, expr);
        assert!(!conds.is_empty(), "{report:#}");
        for cond in conds {
            let right = &cond["right"];
            assert_eq!(right["truncated"], true, "{cond:#}");
            assert_eq!(right["length"], 1000, "{cond:#}");
            let kept = right["value"].as_array().unwrap();
            assert!(!kept.is_empty() && kept.len() <= 100, "kept {}", kept.len());
            assert_eq!(kept[0], 0);
            assert_eq!(right["provenance"], "input.huge");
            // The scalar side is never truncated.
            assert!(cond["left"].get("truncated").is_none(), "{cond:#}");
            assert!(cond["left"].get("length").is_none(), "{cond:#}");
        }
    }
}

#[test]
fn rg5_nested_collections_share_one_truncation_budget() {
    // 20 inner arrays of 20 = 420 nodes; the budget must bound the total, not each level.
    let body = "input.grid != []";
    let policy =
        format!("package bicep\nimport rego.v1\ndeny contains \"v\" if {{\n    {body}\n}}\n");
    let grid: Vec<Vec<u32>> = (0..20).map(|_| (0..20).collect()).collect();
    let input = serde_json::json!({ "grid": grid }).to_string();
    let (result, report) = run_rg1_case(
        &policy,
        &input,
        rg5_settings(evaluation_trace::ConditionMode::PrimaryOnly),
    );
    assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
    let conds = rg5_conditions(&report, body);
    assert!(!conds.is_empty(), "{report:#}");
    for cond in conds {
        let left = &cond["left"];
        assert_eq!(left["truncated"], true, "{cond:#}");
        assert_eq!(left["length"], 20, "{cond:#}");
        let total: usize = left["value"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| 1 + row.as_array().map_or(0, Vec::len))
            .sum();
        assert!(total <= 100, "kept {total} nodes: {cond:#}");
        // The empty-array side is small and untouched.
        assert!(cond["right"].get("truncated").is_none(), "{cond:#}");
    }

    // Control: a small nested value is reported verbatim.
    let (_, small) = run_rg1_case(
        &policy,
        r#"{"grid":[[1,2],[3]]}"#,
        rg5_settings(evaluation_trace::ConditionMode::PrimaryOnly),
    );
    let cond = rg5_conditions(&small, body);
    assert!(!cond.is_empty(), "{small:#}");
    assert_eq!(cond[0]["left"]["value"], serde_json::json!([[1, 2], [3]]));
    assert!(cond[0]["left"].get("truncated").is_none());
}

#[test]
fn rg5_compound_keys_count_toward_truncation_budget() {
    let huge: Vec<u32> = (0..1000).collect();
    let input = serde_json::json!({ "huge": huge, "small": [1, 2] }).to_string();
    for body in ["{input.huge: 1} != {}", "[{input.huge: 1}] != []"] {
        let policy =
            format!("package bicep\nimport rego.v1\ndeny contains \"v\" if {{\n    {body}\n}}\n");
        for mode in [
            evaluation_trace::ValueMode::Full,
            evaluation_trace::ValueMode::Redacted,
        ] {
            let (result, report) = run_rg1_case(
                &policy,
                &input,
                evaluation_trace::ExplanationSettings {
                    enabled: true,
                    detail: evaluation_trace::ExplanationDetail::Full,
                    value_mode: mode,
                    ..Default::default()
                },
            );
            assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
            let conds = rg5_conditions(&report, body);
            assert!(!conds.is_empty(), "{report:#}");
            for cond in conds {
                assert_eq!(cond["left"]["truncated"], true, "{body}: {cond:#}");
                assert_eq!(cond["left"]["length"], 1, "{body}: {cond:#}");
                assert!(
                    !cond.to_string().contains("999"),
                    "{body}: the oversized key was emitted: {cond:#}"
                );
            }
        }
    }

    // Control: a small compound key fits and is kept whole.
    let body = "{input.small: 1} != {}";
    let (_, small) = run_rg1_case(
        &format!("package bicep\nimport rego.v1\ndeny contains \"v\" if {{\n    {body}\n}}\n"),
        &input,
        rg5_settings(evaluation_trace::ConditionMode::PrimaryOnly),
    );
    let cond = rg5_conditions(&small, body);
    assert!(!cond.is_empty(), "{small:#}");
    assert!(cond[0]["left"].get("truncated").is_none(), "{small:#}");
    assert_eq!(
        cond[0]["left"]["value"].as_object().map(|o| o.len()),
        Some(1)
    );
}

#[test]
fn rg5_redaction_fails_closed_on_compound_object_keys() {
    let body = "{input.profile: 1} != {}";
    let policy =
        format!("package bicep\nimport rego.v1\ndeny contains \"v\" if {{\n    {body}\n}}\n");
    let redacted = evaluation_trace::ExplanationSettings {
        enabled: true,
        detail: evaluation_trace::ExplanationDetail::Full,
        value_mode: evaluation_trace::ValueMode::Redacted,
        ..Default::default()
    };
    let (result, report) = run_rg1_case(
        &policy,
        r#"{"profile":{"password":"hunter2"}}"#,
        redacted.clone(),
    );
    assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
    assert!(!rg5_conditions(&report, body).is_empty(), "{report:#}");
    assert!(!report.to_string().contains("hunter2"), "{report:#}");

    // Negative control: a harmless compound key is kept.
    let (_, harmless) = run_rg1_case(&policy, r#"{"profile":{"name":"alice"}}"#, redacted);
    assert!(harmless.to_string().contains("alice"), "{harmless:#}");
}

#[test]
fn rg5_comparison_capture_stops_at_rule_definition_boundary() {
    // Registers restart per definition: the second definition's guard on
    // `input.flag` must not pick up the first definition's `a == a`.
    let policy = r#"
package bicep
import rego.v1
f(a) := a if {
    a == a
}
f(_) if {
    input.flag
}
deny contains "v" if {
    f(true)
}
"#;
    let (result, report) = run_rg1_case(
        policy,
        r#"{"flag":true}"#,
        rg5_settings(evaluation_trace::ConditionMode::AllContributing),
    );
    assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
    let mut seen = 0;
    for rule in report["rules"].as_array().into_iter().flatten() {
        for def in rule["definitions"].as_array().into_iter().flatten() {
            for cond in def["conditions"].as_array().into_iter().flatten() {
                if cond["text"] == "input.flag" {
                    seen += 1;
                    assert_eq!(cond["kind"], "truthiness", "{cond:#}");
                    assert_eq!(cond["left"]["value"], true, "{cond:#}");
                    assert!(cond.get("right").is_none(), "{cond:#}");
                }
            }
        }
    }
    // The helper's own definitions may not surface as a top-level rule; also
    // check the whole report never shows the input object as a comparison operand.
    let text = report.to_string();
    assert!(
        seen > 0 || !text.contains(r#""value":{"flag":true}"#),
        "stale capture of the whole input: {report:#}"
    );
    assert!(
        !text.contains(r#""value":{"flag":true}"#),
        "stale capture of the whole input: {report:#}"
    );
}

#[test]
fn rg5_comparison_capture_does_not_cross_rule_definitions() {
    // A later definition's first guard must not pick up an `Eq` emitted at the
    // end of the previous definition into the same (reused) register number.
    let policy = r#"
package bicep
import rego.v1
deny contains "eq" if {
    input.a == 1
}
deny contains "truthy" if {
    input.flag
}
"#;
    let (result, report) = run_rg1_case(
        policy,
        r#"{"a":1,"flag":true}"#,
        rg5_settings(evaluation_trace::ConditionMode::AllContributing),
    );
    assert_eq!(result.as_set().unwrap().len(), 2, "{report:#}");
    let conds = rg5_conditions(&report, "input.flag");
    assert!(!conds.is_empty(), "{report:#}");
    for cond in conds {
        assert_eq!(cond["kind"], "truthiness", "{cond:#}");
        assert_eq!(cond["left"]["value"], true, "{cond:#}");
        assert!(cond.get("right").is_none(), "{cond:#}");
    }
}

#[test]
fn rg5_non_comparison_guards_keep_their_shape() {
    let policy = r#"
package bicep
import rego.v1
deny contains r.name if {
    some r in input.resources
    r.enabled
    startswith(r.name, "sa")
    not r.kind == "KeyVault"
}
"#;
    let (result, report) = run_rg1_case(
        policy,
        r#"{"resources":{"sa":{"name":"sa1","enabled":true,"kind":"StorageV2"}}}"#,
        rg5_settings(evaluation_trace::ConditionMode::PrimaryOnly),
    );
    assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");

    let truthy = rg5_conditions(&report, "r.enabled");
    assert!(!truthy.is_empty(), "missing `r.enabled`: {report:#}");
    for cond in truthy {
        assert_eq!(cond["kind"], "truthiness");
        assert_eq!(cond["left"]["value"], true, "{cond:#}");
        assert!(cond.get("right").is_none(), "{cond:#}");
    }
    let builtin = rg5_conditions(&report, "startswith(r.name, \"sa\")");
    assert!(!builtin.is_empty(), "missing startswith: {report:#}");
    for cond in builtin {
        assert_eq!(cond["builtin_name"], "startswith");
        rg5_assert_operand(
            cond,
            "left",
            serde_json::json!("sa1"),
            Some("input.resources.sa.name"),
        );
        rg5_assert_operand(cond, "right", serde_json::json!("sa"), None);
    }
    let negated = rg5_conditions(&report, "not r.kind == \"KeyVault\"");
    assert!(
        !negated.is_empty(),
        "missing negated comparison: {report:#}"
    );
    for cond in negated {
        assert_eq!(cond["negated"], true);
        rg5_assert_operand(
            cond,
            "left",
            serde_json::json!("StorageV2"),
            Some("input.resources.sa.kind"),
        );
        rg5_assert_operand(cond, "right", serde_json::json!("KeyVault"), None);
    }
}

/// Every condition in the report (emissions and definitions).
fn rg2_all(report: &serde_json::Value) -> Vec<&serde_json::Value> {
    let mut out = Vec::new();
    for rule in report["rules"].as_array().into_iter().flatten() {
        for list in ["emissions", "definitions"] {
            for entry in rule[list].as_array().into_iter().flatten() {
                out.extend(entry["conditions"].as_array().into_iter().flatten());
            }
        }
    }
    out
}

fn rg2_scopes(cond: &serde_json::Value) -> Vec<&str> {
    cond.get("scopes")
        .and_then(|s| s.as_array())
        .map(|s| s.iter().filter_map(|v| v.as_str()).collect())
        .unwrap_or_default()
}

const RG2_INPUT: &str = r#"{"resources":{"a":{"name":"a","type":"S"},"b":{"name":"b","type":"S"},"c":{"name":"c","type":"K","flag":true}}}"#;

/// Run `policy` and assert each condition's scopes via `expect`, which returns
/// `None` for conditions it does not classify. Every classified bucket must be hit.
fn rg2_check(
    policy: &str,
    expect: impl Fn(&serde_json::Value) -> Option<(&'static str, Vec<&'static str>)>,
    buckets: &[&str],
) {
    let (_, report) = run_rg1_case(
        policy,
        RG2_INPUT,
        rg5_settings(evaluation_trace::ConditionMode::AllContributing),
    );
    let mut seen = std::collections::BTreeSet::new();
    for cond in rg2_all(&report) {
        if let Some((bucket, scopes)) = expect(cond) {
            seen.insert(bucket);
            assert_eq!(rg2_scopes(cond), scopes, "[{bucket}] {cond:#}");
        }
    }
    for bucket in buckets {
        assert!(
            seen.contains(bucket),
            "bucket `{bucket}` never matched: {report:#}"
        );
    }
}

#[test]
fn rg2_comprehension_conditions_are_scoped_one_line_and_multi_line() {
    // One-line form: every inner condition shares the outer line's text, so
    // only `scopes` (and the binding name) can tell them apart.
    rg2_check(
        "package bicep\nimport rego.v1\ndeny contains msg if {\n    storage := [r | some r in input.resources; r.type == \"S\"]\n    count(storage) > 1\n    msg := sprintf(\"%d\", [count(storage)])\n}\n",
        |c| match (c["location"]["row"].as_u64(), c["binding_name"].as_str()) {
            (Some(4), Some("storage")) => Some(("result binding", vec![])),
            (Some(4), _) => Some(("inner", vec!["comprehension"])),
            (Some(5 | 6), _) => Some(("rule level", vec![])),
            _ => None,
        },
        &["result binding", "inner", "rule level"],
    );
    // Multi-line form (proof shape R6): the inner `some` renders as its own line.
    rg2_check(
        "package bicep\nimport rego.v1\ndeny contains msg if {\n    storage := [r |\n        some r in input.resources\n        r.type == \"S\"\n    ]\n    count(storage) > 1\n    msg := sprintf(\"%d\", [count(storage)])\n}\n",
        |c| match c["location"]["row"].as_u64() {
            Some(5 | 6) => Some(("inner", vec!["comprehension"])),
            Some(4 | 8 | 9) => Some(("rule level", vec![])),
            _ => None,
        },
        &["inner", "rule level"],
    );
}

#[test]
fn rg2_set_and_object_comprehensions_and_inner_negation() {
    rg2_check(
        "package bicep\nimport rego.v1\ndeny contains \"v\" if {\n    names := {r.name | some r in input.resources}\n    m := {r.name: r.type | some r in input.resources}\n    flagged := [r | some r in input.resources; not r.flag]\n    count(names) + count(m) + count(flagged) > 0\n}\n",
        |c| match (c["location"]["row"].as_u64(), c["binding_name"].as_str()) {
            (Some(4..=6), Some("names" | "m" | "flagged")) => Some(("result bindings", vec![])),
            (Some(4..=6), _) => Some(("inner", vec!["comprehension"])),
            (Some(7), _) => Some(("rule level", vec![])),
            _ => None,
        },
        &["result bindings", "inner", "rule level"],
    );
}

#[test]
fn rg2_every_body_and_nested_comprehension_are_scoped() {
    rg2_check(
        "package bicep\nimport rego.v1\ndeny contains \"v\" if {\n    every r in input.resources {\n        r.name != \"\"\n    }\n}\n",
        |c| match c["location"]["row"].as_u64() {
            Some(5) => Some(("body", vec!["every"])),
            Some(4) => Some(("every holds", vec![])),
            _ => None,
        },
        &["body", "every holds"],
    );
    rg2_check(
        "package bicep\nimport rego.v1\ndeny contains \"v\" if {\n    every r in input.resources {\n        names := [n | some n in [r.name]; n != \"\"]\n        count(names) == 1\n    }\n}\n",
        |c| match (c["location"]["row"].as_u64(), c["binding_name"].as_str()) {
            (Some(5), Some("names")) => Some(("every-level binding", vec!["every"])),
            (Some(5), _) => Some(("nested", vec!["every", "comprehension"])),
            (Some(6), _) => Some(("every-level check", vec!["every"])),
            (Some(4), _) => Some(("every holds", vec![])),
            _ => None,
        },
        &["every-level binding", "nested", "every-level check", "every holds"],
    );
}

#[test]
fn rg2_comprehension_inside_negation_is_scoped_but_negated_guard_is_not() {
    rg2_check(
        "package bicep\nimport rego.v1\ndeny contains \"v\" if {\n    not count([r | some r in input.resources; r.type == \"Z\"]) > 0\n}\n",
        |c| {
            let negated_guard = c["kind"] == "comparison" && c["outcome"] == "success";
            Some(if negated_guard {
                ("negated guard", vec![])
            } else {
                ("inner", vec!["negation", "comprehension"])
            })
        },
        &["negated guard", "inner"],
    );
}

#[test]
fn rg2_standard_dedupe_keeps_same_text_conditions_in_different_scopes() {
    // On one line, the outer `input.flag` guard and the one inside the
    // comprehension share text, kind and operands; only the scope differs.
    let (result, report) = run_rg1_case(
        "package bicep\nimport rego.v1\ndeny contains \"v\" if { input.flag; xs := [1 | input.flag]; count(xs) == 1 }\n",
        r#"{"flag":true}"#,
        evaluation_trace::ExplanationSettings {
            enabled: true,
            detail: evaluation_trace::ExplanationDetail::Standard,
            value_mode: evaluation_trace::ValueMode::Full,
            ..Default::default()
        },
    );
    assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
    let emission = &report["rules"][0]["emissions"][0]["conditions"];
    let flag_guards: Vec<Vec<&str>> = emission
        .as_array()
        .unwrap()
        .iter()
        .filter(|c| c["kind"] == "truthiness" && c["left"]["provenance"] == "input.flag")
        .map(rg2_scopes)
        .collect();
    assert!(
        flag_guards.contains(&vec![]),
        "outer guard missing: {report:#}"
    );
    assert!(
        flag_guards.contains(&vec!["comprehension"]),
        "inner guard merged away: {report:#}"
    );
}

#[test]
fn rg2_helpers_some_in_every_nested_every_and_definitions() {
    // A helper call inside `every` is scoped; the helper's own body is
    // analyzed per definition, so its conditions are relative to the helper.
    let (_, report) = run_rg1_case(
        "package bicep\nimport rego.v1\nok(r) if {\n    r.type != \"\"\n}\ndeny contains \"v\" if {\n    every r in input.resources {\n        ok(r)\n    }\n}\n",
        RG2_INPUT,
        rg5_settings(evaluation_trace::ConditionMode::AllContributing),
    );
    let calls: Vec<_> = rg2_all(&report)
        .into_iter()
        .filter(|c| c["text"] == "ok(r)")
        .collect();
    assert!(!calls.is_empty(), "{report:#}");
    for call in calls {
        assert_eq!(rg2_scopes(call), vec!["every"], "{call:#}");
        let inner = call["helper_conditions"]
            .as_array()
            .unwrap_or_else(|| panic!("helper call must expand its body: {call:#}"));
        assert!(
            inner.iter().any(|c| c["text"] == "r.type != \"\""),
            "helper body condition missing: {call:#}"
        );
        for inner in inner {
            assert!(inner.get("scopes").is_none(), "{inner:#}");
        }
    }

    // `some` inside `every` emits its own guard, which is inside the body.
    rg2_check(
        "package bicep\nimport rego.v1\ndeny contains \"v\" if {\n    every r in input.resources {\n        some t in [r.type]\n        t != \"\"\n    }\n}\n",
        |c| match c["location"]["row"].as_u64() {
            Some(5 | 6) => Some(("body", vec!["every"])),
            Some(4) => Some(("every holds", vec![])),
            _ => None,
        },
        &["body", "every holds"],
    );

    // Nested `every`: the inner holds-guard is inside the outer body.
    rg2_check(
        "package bicep\nimport rego.v1\ndeny contains \"v\" if {\n    every r in input.resources {\n        every c in [r.name] {\n            c != \"\"\n        }\n    }\n}\n",
        |c| match c["location"]["row"].as_u64() {
            Some(6) => Some(("inner body", vec!["every", "every"])),
            Some(5) => Some(("inner holds", vec!["every"])),
            Some(4) => Some(("outer holds", vec![])),
            _ => None,
        },
        &["inner body", "inner holds", "outer holds"],
    );

    // A second definition of the same rule starts with a clean scope stack.
    rg2_check(
        "package bicep\nimport rego.v1\ndeny contains \"a\" if {\n    xs := [r | some r in input.resources]\n    count(xs) > 0\n}\ndeny contains \"b\" if {\n    some r in input.resources\n    r.type == \"K\"\n}\n",
        |c| match (c["location"]["row"].as_u64(), c["binding_name"].as_str()) {
            (Some(4), Some("xs")) => Some(("result binding", vec![])),
            (Some(4), _) => Some(("first definition inner", vec!["comprehension"])),
            (Some(9 | 10), _) => Some(("second definition", vec![])),
            _ => None,
        },
        &["result binding", "first definition inner", "second definition"],
    );
}

#[test]
fn rg2_loops_hoisted_out_of_a_negation_keep_their_executed_scope() {
    // `not xs[_]` hoists the `[_]` loop -- and the comprehension producing
    // `xs` -- ahead of the negation, so they execute outside `NegationBegin`.
    // Scopes describe where a condition executes: the comprehension's guard is
    // `["comprehension"]` (still never rule-level), without `negation`.
    let body = "not [true | input.flag][_]";
    let (_, report) = run_rg1_case(
        &format!("package bicep\nimport rego.v1\ndeny contains \"v\" if {{\n    {body}\n}}\n"),
        r#"{"flag": true}"#,
        rg5_settings(evaluation_trace::ConditionMode::AllContributing),
    );
    let inner: Vec<_> = rg2_all(&report)
        .into_iter()
        .filter(|c| c["text"] == body && c["outcome"] == "success")
        .collect();
    assert!(!inner.is_empty(), "{report:#}");
    for cond in inner {
        assert_eq!(rg2_scopes(cond), vec!["comprehension"], "{cond:#}");
    }
}

#[test]
fn rg2_rule_level_conditions_carry_no_scopes() {
    let (_, report) = run_rg1_case(
        "package bicep\nimport rego.v1\ndeny contains r.name if {\n    some r in input.resources\n    r.type == \"S\"\n    not r.flag\n}\n",
        RG2_INPUT,
        rg5_settings(evaluation_trace::ConditionMode::AllContributing),
    );
    let all = rg2_all(&report);
    assert!(all.len() >= 3, "{report:#}");
    for cond in all {
        assert!(cond.get("scopes").is_none(), "{cond:#}");
    }
}

#[test]
fn rg1_negated_comparison_keeps_defined_left_operand_present() {
    let policy = r#"
package bicep
import rego.v1
deny contains "violation" if {
    not input.enabled == input.missing
}
"#;
    let (result, report) = run_rg1_case(
        policy,
        r#"{"enabled":false}"#,
        evaluation_trace::ExplanationSettings {
            enabled: true,
            detail: evaluation_trace::ExplanationDetail::Full,
            ..Default::default()
        },
    );
    assert_eq!(result.as_set().unwrap().len(), 1);
    let condition = find_condition(&report, "not input.enabled == input.missing").unwrap();
    assert_eq!(condition["left"]["provenance"], "input.enabled");
    assert_eq!(condition["left"]["value"], false);
    assert!(condition["left"].get("absent").is_none(), "{condition:#}");
}

#[test]
fn rg1_negated_rule_or_function_result_is_not_reported_absent() {
    for (policy, input, text) in [
        (
            r#"
package bicep
import rego.v1
flag := input.enabled == input.missing
deny contains "v" if {
    not flag
}
"#,
            r#"{"enabled":false}"#,
            "not flag",
        ),
        (
            r#"
package bicep
import rego.v1
bad(r) := r.enabled == input.expected
deny contains "v" if {
    not bad(input.resource)
}
"#,
            r#"{"resource":{"enabled":false}}"#,
            "not bad(input.resource)",
        ),
    ] {
        let (result, report) = run_rg1_case(
            policy,
            input,
            evaluation_trace::ExplanationSettings {
                enabled: true,
                detail: evaluation_trace::ExplanationDetail::Full,
                ..Default::default()
            },
        );
        assert_eq!(result.as_set().unwrap().len(), 1, "{report:#}");
        let condition = find_condition(&report, text).unwrap();
        assert!(
            condition["left"].get("absent").is_none(),
            "a call result is not a missing reference: {condition:#}"
        );
        assert!(
            condition["left"].get("provenance").is_none(),
            "a call result must not inherit a path from inside the callee: {condition:#}"
        );
    }
}

#[test]
fn rg1_non_reference_negation_does_not_gain_provenance_or_absence() {
    let policy = r#"
package bicep
import rego.v1
deny contains "short" if {
    not count(input.values) > 1
}
"#;
    let (result, report) = run_rg1_case(
        policy,
        r#"{"values":[]}"#,
        evaluation_trace::ExplanationSettings {
            enabled: true,
            detail: evaluation_trace::ExplanationDetail::Full,
            ..Default::default()
        },
    );
    assert_eq!(result.as_set().unwrap().len(), 1);
    let condition = find_condition(&report, "not count(input.values) > 1").unwrap();
    assert_eq!(condition["negated"], true);
    for operand in ["left", "right"] {
        assert!(
            condition[operand].get("provenance").is_none(),
            "{condition:#}"
        );
        assert!(condition[operand].get("absent").is_none(), "{condition:#}");
    }
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
        max_derivations: 1,
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
        max_derivations: 1,
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

// ---------------------------------------------------------------------------
// RG-3: every derivation of a repeated partial-set value (opt-in).
// ---------------------------------------------------------------------------

const RG3_CONSTANT_POLICY: &str = r#"package bicep
import rego.v1

deny contains msg if {
    some r in input.resources
    r.type == "storage"
    not r.properties.tls
    msg := "storage must set tls"
}
"#;

const RG3_CONSTANT_INPUT: &str = r#"{"resources": {
    "a": {"type": "storage", "properties": {}},
    "b": {"type": "storage", "properties": {"tls": "1.2"}},
    "c": {"type": "storage", "properties": {}},
    "d": {"type": "storage", "properties": {}},
    "e": {"type": "vault", "properties": {}}
}}"#;

fn rg3_settings(
    condition_mode: evaluation_trace::ConditionMode,
    max_derivations: usize,
) -> evaluation_trace::ExplanationSettings {
    evaluation_trace::ExplanationSettings {
        enabled: true,
        condition_mode,
        value_mode: evaluation_trace::ValueMode::Full,
        detail: evaluation_trace::ExplanationDetail::Standard,
        max_derivations,
        ..Default::default()
    }
}

fn rg3_emissions(report: &serde_json::Value) -> Vec<&serde_json::Value> {
    let rules = report["rules"].as_array().expect("report must list rules");
    let deny = rules
        .iter()
        .find(|rule| rule["name"] == "data.bicep.deny")
        .expect("deny rule must be explained");
    deny["emissions"]
        .as_array()
        .expect("deny must have emissions")
        .iter()
        .collect()
}

/// The resource keys named, in order, by the RG-1 provenance of the deciding
/// `not r.properties.tls` conditions of one derivation.
fn rg3_subjects(derivation: &serde_json::Value) -> Vec<String> {
    let conditions = derivation["conditions"]
        .as_array()
        .expect("derivation must carry conditions");
    let mut subjects: Vec<String> = conditions
        .iter()
        .filter_map(|condition| condition["left"]["provenance"].as_str())
        .filter_map(|path| path.strip_prefix("input.resources."))
        .filter_map(|rest| rest.strip_suffix(".properties.tls"))
        .map(str::to_string)
        .collect();
    subjects.dedup();
    subjects
}

/// The single subject of a PrimaryOnly derivation.
fn rg3_subject(derivation: &serde_json::Value) -> String {
    let subjects = rg3_subjects(derivation);
    assert_eq!(
        subjects.len(),
        1,
        "each derivation must name exactly one subject: {derivation:#}"
    );
    subjects[0].clone()
}

fn rg3_derivation_subjects(emission: &serde_json::Value) -> Vec<String> {
    emission["derivations"]
        .as_array()
        .unwrap_or_else(|| panic!("emission must carry derivations: {emission:#}"))
        .iter()
        .map(rg3_subject)
        .collect()
}

#[test]
fn rg3_repeated_constant_reports_every_derivation_in_both_condition_modes() {
    for mode in [
        evaluation_trace::ConditionMode::PrimaryOnly,
        evaluation_trace::ConditionMode::AllContributing,
    ] {
        let (result, report) = run_rg1_case(
            RG3_CONSTANT_POLICY,
            RG3_CONSTANT_INPUT,
            rg3_settings(mode, 10),
        );
        assert_eq!(result.as_set().unwrap().len(), 1);
        let emissions = rg3_emissions(&report);
        assert_eq!(emissions.len(), 1, "{mode:?}: one distinct value");
        let emission = emissions[0];
        assert_eq!(emission["result"], "storage must set tls");
        let derivations = emission["derivations"].as_array().unwrap();
        assert_eq!(derivations.len(), 3, "{mode:?}: {emission:#}");
        if mode == evaluation_trace::ConditionMode::PrimaryOnly {
            assert_eq!(
                rg3_derivation_subjects(emission),
                ["a", "c", "d"],
                "every non-compliant resource, in trace order"
            );
        } else {
            // Pre-existing: an AllContributing emission window runs from the
            // start of the body, so it also holds earlier loop iterations.
            // The iteration that emitted is the last one in the window.
            let last: Vec<String> = derivations
                .iter()
                .map(|derivation| rg3_subjects(derivation).pop().unwrap())
                .collect();
            assert_eq!(last, ["a", "c", "d"]);
            assert_eq!(rg3_subjects(&derivations[2]), ["a", "b", "c", "d"]);
        }
        for derivation in derivations {
            assert_eq!(derivation["definition_index"], 0);
        }
        // The top-level fields are exactly the first derivation's.
        assert_eq!(emission["definition_index"], 0);
        assert_eq!(
            emission["conditions"],
            emission["derivations"][0]["conditions"]
        );
        // The `some r` loop is still running when each value is emitted, so
        // its summary belongs to the definition, not to any emission.
        assert!(
            !emission.to_string().contains("\"witness\""),
            "{mode:?}: an unfinished loop must not be reported on an emission: {emission:#}"
        );
        assert!(emission.get("derivation_count").is_none(), "{emission:#}");
        assert!(
            emission.get("derivations_truncated").is_none(),
            "{emission:#}"
        );
    }
}

#[test]
fn rg3_equal_object_results_report_each_derivation() {
    let policy = RG3_CONSTANT_POLICY.replace(
        r#"msg := "storage must set tls""#,
        r#"msg := {"code": "TLS", "severity": 2}"#,
    );
    let (_, report) = run_rg1_case(
        &policy,
        RG3_CONSTANT_INPUT,
        rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10),
    );
    let emissions = rg3_emissions(&report);
    assert_eq!(emissions.len(), 1);
    assert_eq!(emissions[0]["result"]["code"], "TLS");
    assert_eq!(rg3_derivation_subjects(emissions[0]), ["a", "c", "d"]);
}

#[test]
fn rg3_cap_keeps_first_derivations_and_reports_total() {
    for (max, kept, truncated) in [(2_usize, 2_usize, true), (3, 3, false), (4, 3, false)] {
        let (_, report) = run_rg1_case(
            RG3_CONSTANT_POLICY,
            RG3_CONSTANT_INPUT,
            rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, max),
        );
        let emission = rg3_emissions(&report)[0];
        let subjects = rg3_derivation_subjects(emission);
        assert_eq!(subjects.len(), kept, "max={max}: {emission:#}");
        assert_eq!(subjects, ["a", "c", "d"][..kept], "max={max}");
        if truncated {
            assert_eq!(emission["derivation_count"], 3, "max={max}");
            assert_eq!(emission["derivations_truncated"], true, "max={max}");
        } else {
            assert!(emission.get("derivation_count").is_none(), "max={max}");
            assert!(emission.get("derivations_truncated").is_none(), "max={max}");
        }
    }
}

#[test]
fn rg3_default_and_one_and_zero_keep_first_derivation_only() {
    let default_settings = evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode: evaluation_trace::ValueMode::Full,
        detail: evaluation_trace::ExplanationDetail::Standard,
        ..Default::default()
    };
    assert_eq!(default_settings.max_derivations, 1);
    let (_, default_report) =
        run_rg1_case(RG3_CONSTANT_POLICY, RG3_CONSTANT_INPUT, default_settings);
    for max in [0_usize, 1] {
        let (_, report) = run_rg1_case(
            RG3_CONSTANT_POLICY,
            RG3_CONSTANT_INPUT,
            rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, max),
        );
        assert_eq!(report, default_report, "max={max} must equal the default");
    }
    let text = default_report.to_string();
    for field in ["derivations", "derivation_count", "derivations_truncated"] {
        assert!(
            !text.contains(field),
            "default output must not mention {field}"
        );
    }
    let emission = rg3_emissions(&default_report)[0];
    // Unchanged first-derivation explanation: the first non-compliant resource.
    let first = rg3_subject(emission);
    assert_eq!(first, "a");
}

#[test]
fn rg3_distinct_values_carry_one_derivation_each() {
    let policy = RG3_CONSTANT_POLICY
        .replace("some r in input.resources", "some k, r in input.resources")
        .replace(
            r#"msg := "storage must set tls""#,
            r#"msg := sprintf("%s must set tls", [k])"#,
        );
    let (_, report) = run_rg1_case(
        &policy,
        RG3_CONSTANT_INPUT,
        rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10),
    );
    let emissions = rg3_emissions(&report);
    let results: Vec<&serde_json::Value> = emissions.iter().map(|e| &e["result"]).collect();
    assert_eq!(
        results,
        ["a must set tls", "c must set tls", "d must set tls"],
        "{report:#}"
    );
    for (emission, subject) in emissions.iter().zip(["a", "c", "d"]) {
        assert_eq!(rg3_derivation_subjects(emission), [subject]);
        assert!(emission.get("derivation_count").is_none());
    }
}

#[test]
fn rg3_two_definitions_of_the_same_value_keep_their_definition_index() {
    let policy = r#"package bicep
import rego.v1

deny contains "dup" if {
    input.a == 1
}

deny contains "dup" if {
    input.b == 2
}
"#;
    let (_, report) = run_rg1_case(
        policy,
        r#"{"a": 1, "b": 2}"#,
        rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10),
    );
    let emissions = rg3_emissions(&report);
    assert_eq!(emissions.len(), 1);
    let derivations = emissions[0]["derivations"].as_array().unwrap();
    assert_eq!(derivations.len(), 2, "{:#}", emissions[0]);
    let paths: Vec<(&serde_json::Value, &str)> = derivations
        .iter()
        .map(|derivation| {
            let path = derivation["conditions"]
                .as_array()
                .unwrap()
                .iter()
                .find_map(|condition| condition["left"]["provenance"].as_str())
                .expect("derivation must name its input");
            (&derivation["definition_index"], path)
        })
        .collect();
    assert_eq!(paths[0], (&serde_json::json!(0), "input.a"));
    assert_eq!(paths[1], (&serde_json::json!(1), "input.b"));
}

#[test]
fn rg3_single_emission_collects_every_derivation_of_the_target_only() {
    let policy = r#"package bicep
import rego.v1

deny contains "other" if {
    input.z == 1
}

deny contains msg if {
    some r in input.resources
    r.type == "storage"
    not r.properties.tls
    msg := "storage must set tls"
}
"#;
    let input = r#"{"z": 1, "resources": {
        "a": {"type": "storage", "properties": {}},
        "c": {"type": "storage", "properties": {}}
    }}"#;

    let mut by_index = rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10);
    by_index.scope = evaluation_trace::ExplanationScope::SingleEmission;
    by_index.emission_index = Some(1);
    let (_, report) = run_rg1_case(policy, input, by_index);
    let emissions = rg3_emissions(&report);
    assert_eq!(emissions.len(), 1, "{report:#}");
    assert_eq!(emissions[0]["index"], 1);
    assert_eq!(emissions[0]["result"], "storage must set tls");
    assert_eq!(rg3_derivation_subjects(emissions[0]), ["a", "c"]);

    let mut by_value = rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10);
    by_value.scope = evaluation_trace::ExplanationScope::SingleEmission;
    by_value.emission_value = Some(Value::from("storage must set tls"));
    let (_, report) = run_rg1_case(policy, input, by_value);
    let emissions = rg3_emissions(&report);
    assert_eq!(emissions.len(), 1, "{report:#}");
    assert_eq!(rg3_derivation_subjects(emissions[0]), ["a", "c"]);

    let mut other = rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10);
    other.scope = evaluation_trace::ExplanationScope::SingleEmission;
    other.emission_index = Some(0);
    let (_, report) = run_rg1_case(policy, input, other);
    let emissions = rg3_emissions(&report);
    assert_eq!(emissions.len(), 1);
    assert_eq!(emissions[0]["result"], "other");
    assert_eq!(emissions[0]["derivations"].as_array().unwrap().len(), 1);
}

#[test]
fn rg3_complete_rules_and_rule_summary_are_unaffected() {
    let policy = r#"package bicep
import rego.v1

default allow := false

allow if {
    input.a == 1
}

deny contains "x" if {
    some v in input.xs
    v > 0
}
"#;
    let input = r#"{"a": 1, "xs": [1, 2]}"#;
    let mut summary = rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10);
    summary.scope = evaluation_trace::ExplanationScope::RuleSummary;
    let summary_with = rg5_traced_only(policy, input, summary.clone());
    summary.max_derivations = 1;
    let summary_without = rg5_traced_only(policy, input, summary);
    assert_eq!(summary_with, summary_without);
    assert!(!summary_with.to_string().contains("derivations"));

    let mut engine = Engine::new();
    engine.add_policy("rg3.rego".into(), policy.into()).unwrap();
    let compiled = engine
        .compile_with_entrypoint(&Rc::from("data.bicep.allow"))
        .unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &["data.bicep.allow"])
            .unwrap();
    let mut vm = rvm::RegoVM::new_with_policy(compiled);
    vm.load_program(program);
    vm.set_explanation_settings(rg3_settings(
        evaluation_trace::ConditionMode::PrimaryOnly,
        10,
    ));
    vm.set_input(Value::from_json_str(input).unwrap());
    let result = vm.execute_entry_point_by_name("data.bicep.allow").unwrap();
    assert_eq!(result, Value::from(true));
    let report = vm.take_causality_report(result).unwrap();
    assert!(!report.contains("derivations"), "{report}");
}

#[test]
fn rg3_exact_duplicate_derivations_are_dropped_before_counting() {
    let policy = r#"package bicep
import rego.v1

deny contains "x" if {
    some i in [1, 1, 2]
    i == 1
    input.flag
}
"#;
    let (_, report) = run_rg1_case(
        policy,
        r#"{"flag": true}"#,
        rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10),
    );
    let emission = rg3_emissions(&report)[0];
    let derivations = emission["derivations"].as_array().unwrap();
    // The two `i == 1` iterations read the same literal at the same location,
    // so their derivations are equal and count once. Index 0 and 1 of the
    // literal array carry no provenance that could tell them apart.
    assert_eq!(derivations.len(), 1, "{emission:#}");
    assert!(emission.get("derivation_count").is_none(), "{emission:#}");

    // Three equal `i == 1` derivations and one distinct `i == 2` derivation:
    // deduplicated there are 2, which fit a cap of 2. Counting before
    // deduplicating would give 4 and report truncation.
    let counted = policy
        .replace("[1, 1, 2]", "[1, 1, 1, 2]")
        .replace("i == 1", "i >= 1");
    let (_, capped) = run_rg1_case(
        &counted,
        r#"{"flag": true}"#,
        rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 2),
    );
    let capped = rg3_emissions(&capped)[0];
    assert_eq!(
        capped["derivations"].as_array().unwrap().len(),
        2,
        "{capped:#}"
    );
    assert!(capped.get("derivations_truncated").is_none(), "{capped:#}");
    assert!(capped.get("derivation_count").is_none(), "{capped:#}");
}

#[test]
fn rg3_compact_detail_keeps_distinct_derivations() {
    // With `r := input.resources[_]`, Compact keeps only the negation, whose
    // text carries one loop-wide sample, so every derivation prints alike.
    let policy =
        RG3_CONSTANT_POLICY.replace("some r in input.resources", "r := input.resources[_]");
    let mut settings = rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10);
    settings.detail = evaluation_trace::ExplanationDetail::Compact;
    let (_, report) = run_rg1_case(&policy, RG3_CONSTANT_INPUT, settings);
    let emission = rg3_emissions(&report)[0];
    let derivations = emission["derivations"].as_array().unwrap();
    // They are still distinct evidence (resources a, c, d) and are all kept.
    assert_eq!(derivations.len(), 3, "{emission:#}");
    assert_eq!(
        derivations[0], derivations[1],
        "Compact output must look alike"
    );
    // The loop producing these values is unfinished at each emission, so
    // neither view decorates text with its summary.
    assert!(!emission.to_string().contains("[loop:"), "{emission:#}");
    assert_eq!(emission["conditions"], derivations[0]["conditions"]);
    assert!(derivations[0]["conditions"]
        .as_array()
        .unwrap()
        .iter()
        .all(|condition| condition.get("left").is_none()));
    assert!(
        emission.get("derivations_truncated").is_none(),
        "{emission:#}"
    );
}

#[test]
fn rg3_redacted_secret_paths_keep_derivations_distinct() {
    let policy = RG3_CONSTANT_POLICY
        .replace("r.properties.tls", "r.properties.password")
        .replace("storage must set tls", "storage must set a password");
    let mut settings = rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10);
    settings.value_mode = evaluation_trace::ValueMode::Redacted;
    let input = RG3_CONSTANT_INPUT.replace(r#""tls": "1.2""#, r#""password": "hunter2""#);
    let (_, report) = run_rg1_case(&policy, &input, settings);
    let emission = rg3_emissions(&report)[0];
    let paths: Vec<&str> = emission["derivations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|derivation| {
            derivation["conditions"]
                .as_array()
                .unwrap()
                .iter()
                .filter_map(|condition| condition["left"]["provenance"].as_str())
                .find(|path| path.ends_with(".properties.password"))
                .expect("derivation must name the password path")
        })
        .collect();
    assert_eq!(
        paths,
        [
            "input.resources.a.properties.password",
            "input.resources.c.properties.password",
            "input.resources.d.properties.password"
        ]
    );
}

#[test]
fn rg3_redacted_derivations_sanitize_secrets_nested_in_unary_operands() {
    // Only `c`, a middle derivation, nests a secret. The `some r` binding
    // carries the whole resource as a single operand.
    let input = r#"{"resources": {
        "a": {"type": "storage", "properties": {}},
        "b": {"type": "storage", "properties": {"tls": "1.2"}},
        "c": {"type": "storage", "properties": {}, "auth": {"password": "hunter2"}},
        "d": {"type": "storage", "properties": {}}
    }}"#;
    for (value_mode, exposed) in [
        (evaluation_trace::ValueMode::Full, true),
        (evaluation_trace::ValueMode::Redacted, false),
    ] {
        let mut settings = rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10);
        settings.value_mode = value_mode;
        let (_, report) = run_rg1_case(RG3_CONSTANT_POLICY, input, settings);
        let emission = rg3_emissions(&report)[0];
        assert_eq!(rg3_derivation_subjects(emission), ["a", "c", "d"]);
        // The whole report, not only the derivations, follows the value mode.
        let text = report.to_string();
        assert_eq!(text.contains("hunter2"), exposed, "{value_mode:?}: {text}");
        if !exposed {
            let binding = emission["derivations"][1]["conditions"]
                .as_array()
                .unwrap()
                .iter()
                .find(|condition| condition["left"]["provenance"] == "input.resources.c")
                .expect("c's derivation binds the resource");
            assert_eq!(binding["left"]["redacted"], true);
            assert_eq!(binding["left"]["value"]["auth"]["password"], "<redacted>");
            assert_eq!(binding["left"]["value"]["type"], "storage");
        }
    }
}

#[test]
fn rg3_partial_object_rules_carry_no_derivations() {
    let policy = r#"package bicep
import rego.v1

deny[k] := "must set tls" if {
    some k, r in input.resources
    not r.properties.tls
}
"#;
    let report = rg5_traced_only(
        policy,
        RG3_CONSTANT_INPUT,
        rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10),
    );
    let rule = &report["rules"][0];
    assert_eq!(rule["type"], "partial_object", "{report:#}");
    // Only partial-set rules report emissions, so there is nothing to expand.
    assert_eq!(rule["result"].as_object().map(|m| m.len()), Some(4));
    assert!(rule.get("emissions").is_none(), "{report:#}");
    assert!(!report.to_string().contains("derivation"), "{report:#}");
}
#[test]
fn rg3_exhausted_value_capture_marks_derivations_incomplete() {
    let policy = r#"package bicep
import rego.v1

deny contains "nonnegative" if {
    some v in input.xs
    v >= 0
}
"#;
    // Ten matches, then enough failing comparisons (each capturing operands) to
    // exhaust the value table, then ten more matches whose emitted values can
    // no longer be captured.
    let mut xs = vec!["0"; 10];
    xs.extend(vec!["-1"; 40_000]);
    xs.extend(vec!["0"; 10]);
    let input = format!(r#"{{"xs": [{}]}}"#, xs.join(","));
    let mut engine = Engine::new();
    engine.add_policy("rg3.rego".into(), policy.into()).unwrap();
    let compiled = engine
        .compile_with_entrypoint(&Rc::from("data.bicep.deny"))
        .unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &["data.bicep.deny"])
            .unwrap();
    // A cap above the number found shows truncation is reported for the
    // incomplete trace itself, not just for exceeding the cap.
    for cap in [5_usize, 100] {
        let mut vm = rvm::RegoVM::new_with_policy(compiled.clone());
        vm.load_program(program.clone());
        vm.set_max_instructions(usize::MAX);
        vm.set_explanation_settings(rg3_settings(
            evaluation_trace::ConditionMode::PrimaryOnly,
            cap,
        ));
        vm.set_input(Value::from_json_str(&input).unwrap());
        let result = vm.execute_entry_point_by_name("data.bicep.deny").unwrap();
        let report: serde_json::Value =
            serde_json::from_str(&vm.take_causality_report(result).unwrap()).unwrap();
        let emission = rg3_emissions(&report)[0];
        assert_eq!(emission["result"], "nonnegative");
        // Only the ten derivations recorded before the table filled are found.
        assert_eq!(emission["derivation_count"], 10, "cap {cap}");
        assert_eq!(emission["derivations_truncated"], true, "cap {cap}");
        let kept = emission["derivations"].as_array().unwrap().len();
        assert_eq!(kept, cap.min(10), "cap {cap}");
    }
}
#[test]
fn rg3_duplicates_beyond_the_cap_are_counted_once() {
    let policy = r#"package bicep
import rego.v1

deny contains "x" if {
    some i in [1, 2, 1, 3, 3]
    i >= 1
    input.flag
}
"#;
    let (_, report) = run_rg1_case(
        policy,
        r#"{"flag": true}"#,
        rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 2),
    );
    let emission = rg3_emissions(&report)[0];
    // Distinct derivations: i = 1, 2, 3. The repeated 1 matches a kept entry;
    // the repeated 3 matches one past the cap.
    assert_eq!(emission["derivations"].as_array().unwrap().len(), 2);
    assert_eq!(emission["derivation_count"], 3, "{emission:#}");
    assert_eq!(emission["derivations_truncated"], true);
}

#[test]
fn rg3_unrelated_capture_exhaustion_keeps_deduplication() {
    let policy = r#"package bicep
import rego.v1

deny contains "x" if {
    some i in [1, 1, 2]
    i == 1
    input.flag
}

deny contains "x" if {
    some n in input.padding
    n == -1
}
"#;
    let padding = vec!["0"; 40_000].join(",");
    let input = format!(r#"{{"flag": true, "padding": [{padding}]}}"#);
    let mut engine = Engine::new();
    engine.add_policy("rg3.rego".into(), policy.into()).unwrap();
    let compiled = engine
        .compile_with_entrypoint(&Rc::from("data.bicep.deny"))
        .unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &["data.bicep.deny"])
            .unwrap();
    let mut vm = rvm::RegoVM::new_with_policy(compiled);
    vm.load_program(program);
    vm.set_max_instructions(usize::MAX);
    vm.set_explanation_settings(rg3_settings(
        evaluation_trace::ConditionMode::PrimaryOnly,
        2,
    ));
    vm.set_input(Value::from_json_str(&input).unwrap());
    let result = vm.execute_entry_point_by_name("data.bicep.deny").unwrap();
    let report: serde_json::Value =
        serde_json::from_str(&vm.take_causality_report(result).unwrap()).unwrap();
    let emission = rg3_emissions(&report)[0];
    // The second definition fills the value table but never emits, so the
    // first definition's two equal derivations are still one.
    assert_eq!(
        emission["derivations"].as_array().unwrap().len(),
        1,
        "{emission:#}"
    );
    assert!(
        emission.get("derivations_truncated").is_none(),
        "{emission:#}"
    );
    assert!(emission.get("derivation_count").is_none(), "{emission:#}");
}

#[test]
fn rg3_fingerprint_distinguishes_arrays_from_sets_beyond_the_cap() {
    let policy = r#"package bicep
import rego.v1

deny contains "x" if {
    some i in [0, 1, [2], {2}]
    i != null
    input.flag
}
"#;
    let (_, report) = run_rg1_case(
        policy,
        r#"{"flag": true}"#,
        rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 2),
    );
    let emission = rg3_emissions(&report)[0];
    // `[2]` and `{2}` serialize to the same JSON but are different values, so
    // the two derivations past the cap are both counted.
    assert_eq!(emission["derivation_count"], 4, "{emission:#}");
    assert_eq!(emission["derivations_truncated"], true);
    assert_eq!(emission["derivations"].as_array().unwrap().len(), 2);
}

#[test]
fn rg3_fingerprint_counts_large_integers_exactly_and_equal_numbers_once() {
    // Past a cap of 2: two integers beyond 64 bits that JSON rounds to the same
    // f64 are distinct; `2` and `2.0` are equal numbers and count once.
    for (values, expected) in [
        ("[0, 1, 18446744073709551616, 18446744073709551617]", 4),
        ("[0, 1, 2, 2.0]", 3),
    ] {
        let policy = format!(
            "package bicep\nimport rego.v1\n\ndeny contains \"x\" if {{\n    some i in {values}\n    i != null\n    input.flag\n}}\n"
        );
        let (_, report) = run_rg1_case(
            &policy,
            r#"{"flag": true}"#,
            rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 2),
        );
        let emission = rg3_emissions(&report)[0];
        assert_eq!(
            emission["derivation_count"], expected,
            "{values}: {emission:#}"
        );
        assert_eq!(emission["derivations_truncated"], true, "{values}");
    }
}

#[test]
fn rg3_compact_detail_counts_distinct_derivations_beyond_the_cap() {
    let policy =
        RG3_CONSTANT_POLICY.replace("some r in input.resources", "r := input.resources[_]");
    let input = r#"{"resources": {
        "a": {"type": "storage", "properties": {}},
        "c": {"type": "storage", "properties": {}},
        "d": {"type": "storage", "properties": {}},
        "f": {"type": "storage", "properties": {}}
    }}"#;
    let mut settings = rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 2);
    settings.detail = evaluation_trace::ExplanationDetail::Compact;
    let (_, report) = run_rg1_case(&policy, input, settings);
    let emission = rg3_emissions(&report)[0];
    // The two derivations past the cap print like the kept ones but are
    // distinct resources, so the fingerprint must use the unstripped view.
    assert_eq!(emission["derivations"].as_array().unwrap().len(), 2);
    assert_eq!(emission["derivation_count"], 4, "{emission:#}");
}

#[test]
fn rg3_derivations_report_their_own_finished_inner_loop() {
    let policy = r#"package bicep
import rego.v1

deny contains "ports are positive" if {
    some r in input.resources
    every p in r.ports {
        p > 0
    }
}
"#;
    let input = r#"{"resources": {"a": {"ports": [1, 2]}, "b": {"ports": [3]}}}"#;
    for mode in [
        evaluation_trace::ConditionMode::PrimaryOnly,
        evaluation_trace::ConditionMode::AllContributing,
    ] {
        let (_, report) = run_rg1_case(policy, input, rg3_settings(mode, 10));
        let emission = rg3_emissions(&report)[0];
        let derivations = emission["derivations"].as_array().unwrap();
        assert_eq!(derivations.len(), 2, "{mode:?}: {emission:#}");
        assert_eq!(emission["conditions"], derivations[0]["conditions"]);
        // Each derivation's `every` loop finished before its value was
        // emitted, so each carries that loop's own summary, never another
        // iteration's and never the unfinished outer `some r` loop.
        let witnesses: Vec<(u64, u64, &serde_json::Value)> = derivations
            .iter()
            .map(|derivation| {
                let found: Vec<&serde_json::Value> = derivation["conditions"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .filter_map(|condition| condition.get("witness"))
                    .collect();
                assert_eq!(found.len(), 1, "{mode:?}: {derivation:#}");
                (
                    found[0]["total_iterations"].as_u64().unwrap(),
                    found[0]["success_count"].as_u64().unwrap(),
                    &found[0]["sample_value"],
                )
            })
            .collect();
        assert_eq!(witnesses[0], (2, 2, &serde_json::json!(1)), "{mode:?}");
        assert_eq!(witnesses[1], (1, 1, &serde_json::json!(3)), "{mode:?}");
    }
}

// ---------------------------------------------------------------------------
// RG-R2: Redacted mode sanitizes every reported value, not only two-operand
// conditions. RG-W1: a loop witness only describes a loop that finished
// within what it explains.
// ---------------------------------------------------------------------------

// The causality demo's "Reason capture without leaking secrets" scenario.
const RGW_DEMO_POLICY: &str = r#"package demo
import rego.v1

violations contains msg if {
    request := input.requests[_]
    api_token := request.api_token
    request.path == "/admin"
    request.user != "admin"
    msg := sprintf("user %v attempted admin path", [request.user])
}

violations contains msg if {
    request := input.requests[_]
    password := request.password
    count(password) > 0
    request.path == "/login"
    request.user == "guest"
    msg := "guest login included password"
}
"#;

const RGW_DEMO_INPUT: &str = r#"{"requests": [
    {"user": "alice", "path": "/admin", "api_token": "tok-prod-123", "password": ""},
    {"user": "guest", "path": "/login", "api_token": "", "password": "guest-password"}
]}"#;

/// Run `entry` through the interpreter, a plain VM and a traced VM, require
/// equal results, and return the traced report.
fn rgw_run(
    policy: &str,
    input: &str,
    entry: &str,
    settings: evaluation_trace::ExplanationSettings,
) -> serde_json::Value {
    let mut engine = Engine::new();
    engine.add_policy("rgw.rego".into(), policy.into()).unwrap();
    let input = Value::from_json_str(input).unwrap();
    engine.set_input(input.clone());
    let interpreted = engine.eval_rule(entry.into()).unwrap();
    let compiled = engine.compile_with_entrypoint(&Rc::from(entry)).unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entry]).unwrap();
    let mut plain = rvm::RegoVM::new_with_policy(compiled.clone());
    plain.load_program(program.clone());
    plain.set_input(input.clone());
    assert_eq!(
        plain.execute_entry_point_by_name(entry).unwrap(),
        interpreted
    );
    let mut traced = rvm::RegoVM::new_with_policy(compiled);
    traced.load_program(program);
    traced.set_explanation_settings(settings);
    traced.set_input(input);
    let result = traced.execute_entry_point_by_name(entry).unwrap();
    assert_eq!(result, interpreted);
    serde_json::from_str(&traced.take_causality_report(result).unwrap()).unwrap()
}

fn rgw_settings(
    condition_mode: evaluation_trace::ConditionMode,
    detail: evaluation_trace::ExplanationDetail,
    value_mode: evaluation_trace::ValueMode,
) -> evaluation_trace::ExplanationSettings {
    evaluation_trace::ExplanationSettings {
        enabled: true,
        condition_mode,
        detail,
        value_mode,
        ..Default::default()
    }
}

fn rgw_rule<'a>(report: &'a serde_json::Value, name: &str) -> &'a serde_json::Value {
    report["rules"]
        .as_array()
        .unwrap()
        .iter()
        .find(|rule| rule["name"] == name)
        .unwrap_or_else(|| panic!("rule {name} must be explained: {report:#}"))
}

/// The witnesses on a condition list, in order.
fn rgw_witnesses(conditions: &serde_json::Value) -> Vec<&serde_json::Value> {
    conditions
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|condition| condition.get("witness"))
        .collect()
}

const RGW_MODES: [evaluation_trace::ConditionMode; 2] = [
    evaluation_trace::ConditionMode::PrimaryOnly,
    evaluation_trace::ConditionMode::AllContributing,
];

#[test]
fn rgr2_demo_secret_redaction_scenario_leaks_nothing_under_redacted() {
    use evaluation_trace::{ExplanationDetail::*, ValueMode};
    for mode in RGW_MODES {
        for detail in [Standard, Full, Compact] {
            let report = rgw_run(
                RGW_DEMO_POLICY,
                RGW_DEMO_INPUT,
                "data.demo.violations",
                rgw_settings(mode, detail, ValueMode::Redacted),
            );
            let text = report.to_string();
            for secret in ["tok-prod-123", "guest-password"] {
                assert!(
                    !text.contains(secret),
                    "{mode:?}/{detail:?}: {secret} leaked: {report:#}"
                );
            }
            if detail != Compact {
                // Control: the same evidence in Full value mode shows them.
                let full = rgw_run(
                    RGW_DEMO_POLICY,
                    RGW_DEMO_INPUT,
                    "data.demo.violations",
                    rgw_settings(mode, detail, ValueMode::Full),
                )
                .to_string();
                assert!(full.contains("tok-prod-123") && full.contains("guest-password"));
            }
        }
    }

    // The whole-request binding is sanitized in place: secrets replaced,
    // everything else kept, and the operand marked redacted.
    let report = rgw_run(
        RGW_DEMO_POLICY,
        RGW_DEMO_INPUT,
        "data.demo.violations",
        rgw_settings(
            evaluation_trace::ConditionMode::PrimaryOnly,
            evaluation_trace::ExplanationDetail::Standard,
            evaluation_trace::ValueMode::Redacted,
        ),
    );
    let violations = rgw_rule(&report, "data.demo.violations");
    let alice = violations["emissions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|emission| emission["result"] == "user alice attempted admin path")
        .expect("alice's violation must be explained");
    let binding = alice["conditions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|condition| condition["binding_name"] == "request")
        .expect("the request binding must be reported");
    assert_eq!(binding["left"]["provenance"], "input.requests[0]");
    assert_eq!(binding["left"]["redacted"], true);
    assert_eq!(binding["left"]["value"]["api_token"], "<redacted>");
    assert_eq!(binding["left"]["value"]["password"], "<redacted>");
    assert_eq!(binding["left"]["value"]["user"], "alice");
    assert_eq!(binding["left"]["value"]["path"], "/admin");
}

#[test]
fn rgr2_witness_samples_are_redacted_like_operands() {
    use evaluation_trace::{ConditionMode::PrimaryOnly, ExplanationDetail::Standard, ValueMode};
    // (policy body, input, Full-mode sample, Redacted sample key, Redacted sample value)
    let cases = [
        (
            "some r in input.requests\n    r.path == \"/admin\"",
            RGW_DEMO_INPUT,
            serde_json::json!({"user": "alice", "path": "/admin", "api_token": "tok-prod-123", "password": ""}),
            serde_json::json!(0),
            serde_json::json!({"user": "alice", "path": "/admin", "api_token": "<redacted>", "password": "<redacted>"}),
        ),
        (
            // A sensitive collection path hides the element and its key.
            "some t in input.tokens\n    t != \"\"",
            r#"{"tokens": ["", "tok-abc"]}"#,
            serde_json::json!("tok-abc"),
            serde_json::json!("<redacted>"),
            serde_json::json!("<redacted>"),
        ),
        (
            // A sensitive object key hides its value; the key is the name.
            "some k, v in input.config\n    v == \"on\"",
            r#"{"config": {"password": "on", "mode": "off"}}"#,
            serde_json::json!("on"),
            serde_json::json!("password"),
            serde_json::json!("<redacted>"),
        ),
    ];
    for (body, input, full_sample, redacted_key, redacted_sample) in cases {
        let policy = format!("package w\nimport rego.v1\n\nallow if {{\n    {body}\n}}\n");
        let witness_of = |value_mode| {
            let report = rgw_run(
                &policy,
                input,
                "data.w.allow",
                rgw_settings(PrimaryOnly, Standard, value_mode),
            );
            let rule = rgw_rule(&report, "data.w.allow");
            let witnesses = rgw_witnesses(&rule["definitions"][0]["conditions"]);
            assert_eq!(witnesses.len(), 1, "{body}: {report:#}");
            witnesses[0].clone()
        };
        let full = witness_of(ValueMode::Full);
        assert_eq!(full["sample_value"], full_sample, "{body}");
        assert!(full.get("redacted").is_none(), "{body}: {full:#}");
        let redacted = witness_of(ValueMode::Redacted);
        assert_eq!(redacted["sample_key"], redacted_key, "{body}");
        assert_eq!(redacted["sample_value"], redacted_sample, "{body}");
        assert_eq!(redacted["redacted"], true, "{body}");
        assert_eq!(redacted["total_iterations"], full["total_iterations"]);
        assert_eq!(redacted["success_count"], full["success_count"]);
    }
}

#[test]
fn rgw1_emissions_carry_no_unfinished_or_foreign_loop_witness() {
    use evaluation_trace::{ExplanationDetail::*, ValueMode};
    for mode in RGW_MODES {
        for detail in [Standard, Full, Compact] {
            let report = rgw_run(
                RGW_DEMO_POLICY,
                RGW_DEMO_INPUT,
                "data.demo.violations",
                rgw_settings(mode, detail, ValueMode::Full),
            );
            let violations = rgw_rule(&report, "data.demo.violations");
            for emission in violations["emissions"].as_array().unwrap() {
                // Each value is emitted inside its definition's loop, before
                // that loop finishes; no other loop finished inside it.
                assert!(
                    rgw_witnesses(&emission["conditions"]).is_empty(),
                    "{mode:?}/{detail:?}: {emission:#}"
                );
                assert!(!emission.to_string().contains("[loop:"), "{emission:#}");
            }
            if detail == Compact {
                continue;
            }
            // Each definition reports its own loop: alice (key 0) satisfied
            // definition 0, guest (key 1) definition 1.
            let definitions = violations["definitions"].as_array().unwrap();
            assert_eq!(definitions.len(), 2);
            for (definition, key) in definitions.iter().zip([0, 1]) {
                let witnesses = rgw_witnesses(&definition["conditions"]);
                assert_eq!(witnesses.len(), 1, "{mode:?}/{detail:?}: {definition:#}");
                assert_eq!(witnesses[0]["total_iterations"], 2);
                assert_eq!(witnesses[0]["success_count"], 1);
                assert_eq!(witnesses[0]["sample_key"], key, "{definition:#}");
            }
        }
    }
}

#[test]
fn rgw1_outer_loop_summary_stays_on_its_definition() {
    let (_, report) = run_rg1_case(
        RG3_CONSTANT_POLICY,
        RG3_CONSTANT_INPUT,
        rg3_settings(evaluation_trace::ConditionMode::PrimaryOnly, 10),
    );
    let deny = rgw_rule(&report, "data.bicep.deny");
    // No emission or derivation, including the last one, which the loop's
    // exit would otherwise land in.
    assert!(
        !deny["emissions"].to_string().contains("\"witness\""),
        "{deny:#}"
    );
    let witnesses = rgw_witnesses(&deny["definitions"][0]["conditions"]);
    assert_eq!(witnesses.len(), 1, "{deny:#}");
    assert_eq!(witnesses[0]["total_iterations"], 5);
    assert_eq!(witnesses[0]["success_count"], 3);
}

#[test]
fn rgw1_head_function_call_does_not_borrow_another_definitions_loop() {
    let policy = r#"package bicep
import rego.v1

deny contains message_for(r) if {
    some r in input.resources
    r.bad
}

deny contains "other" if {
    some s in input.others
    s.x
}

message_for(r) := msg if {
    r.name != ""
    msg := sprintf("bad %v", [r.name])
}
"#;
    // The matching resource comes last, so the head function's conditions are
    // the last ones recorded before definition 0's loop exits and no reported
    // condition anchors that loop.
    let input = r#"{
        "resources": [{"name": "b", "bad": false}, {"name": "a", "bad": true}],
        "others": [{"x": true}, {"x": true}, {"x": true}]
    }"#;
    for mode in RGW_MODES {
        let report = rgw_run(
            policy,
            input,
            "data.bicep.deny",
            rgw_settings(
                mode,
                evaluation_trace::ExplanationDetail::Standard,
                evaluation_trace::ValueMode::Full,
            ),
        );
        let deny = rgw_rule(&report, "data.bicep.deny");
        // Definition 0 iterates two resources. If it reports a witness, it
        // must be its own loop's, never the three-element `others` loop.
        for witness in rgw_witnesses(&deny["definitions"][0]["conditions"]) {
            assert_eq!(witness["total_iterations"], 2, "{mode:?}: {deny:#}");
        }
        for emission in deny["emissions"].as_array().unwrap() {
            assert!(
                rgw_witnesses(&emission["conditions"]).is_empty(),
                "{emission:#}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// RG-R2 / RG-W1 deep-review round 1: loop ownership, early-failing `every`,
// keyless `every`, assumptions, ARM secret shapes, helper rule results.
// ---------------------------------------------------------------------------

fn rgw_full_standard(
    mode: evaluation_trace::ConditionMode,
) -> evaluation_trace::ExplanationSettings {
    rgw_settings(
        mode,
        evaluation_trace::ExplanationDetail::Standard,
        evaluation_trace::ValueMode::Full,
    )
}

#[test]
fn rgw1_empty_inner_loop_does_not_inherit_the_previous_iterations_loop() {
    let policy = r#"package bicep
import rego.v1

deny contains r.name if {
    some r in input.resources
    every x in r.ports {
        x > 0
    }
}
"#;
    let input = r#"{"resources": [{"name": "a", "ports": [1]}, {"name": "b", "ports": []}]}"#;
    for mode in RGW_MODES {
        let report = rgw_run(policy, input, "data.bicep.deny", rgw_full_standard(mode));
        let deny = rgw_rule(&report, "data.bicep.deny");
        let emission = |name: &str| {
            deny["emissions"]
                .as_array()
                .unwrap()
                .iter()
                .find(|emission| emission["result"] == name)
                .unwrap_or_else(|| panic!("{name} must be emitted: {deny:#}"))
                .clone()
        };
        // `a` ran its own `every` to completion before it was emitted.
        let a = emission("a");
        let a_witnesses = rgw_witnesses(&a["conditions"]);
        assert_eq!(a_witnesses.len(), 1, "{mode:?}: {a:#}");
        assert_eq!(a_witnesses[0]["total_iterations"], 1);
        assert_eq!(a_witnesses[0]["sample_value"], 1);
        // `b`'s `every` had nothing to iterate; `a`'s loop is not its evidence.
        let b = emission("b");
        assert!(
            rgw_witnesses(&b["conditions"]).is_empty(),
            "{mode:?}: {b:#}"
        );
    }
}

#[test]
fn rgw1_head_function_keeps_its_callers_loop_on_the_caller() {
    let policy = r#"package bicep
import rego.v1

deny contains message_for(r) if {
    some r in input.resources
    r.bad
}

message_for(r) := msg if {
    r.name != ""
    msg := sprintf("bad %v", [r.name])
}
"#;
    let input = r#"{"resources": [{"name": "b", "bad": false}, {"name": "a", "bad": true}]}"#;
    for mode in RGW_MODES {
        let report = rgw_run(policy, input, "data.bicep.deny", rgw_full_standard(mode));
        // The caller's loop is summarized on the caller's definition, even
        // though the head function recorded the last condition before it
        // finished.
        let deny = rgw_rule(&report, "data.bicep.deny");
        let witnesses = rgw_witnesses(&deny["definitions"][0]["conditions"]);
        assert_eq!(witnesses.len(), 1, "{mode:?}: {deny:#}");
        assert_eq!(witnesses[0]["total_iterations"], 2);
        assert_eq!(witnesses[0]["success_count"], 1);
        // The head function ran no loop of its own.
        for rule in report["rules"].as_array().unwrap() {
            if rule["name"] == "data.bicep.deny" {
                continue;
            }
            assert!(
                !rule.to_string().contains("\"witness\""),
                "{mode:?}: another rule's loop attributed to {}: {rule:#}",
                rule["name"]
            );
        }
    }
}

#[test]
fn rgw1_early_failing_every_counts_the_failing_iteration() {
    let policy = r#"package bicep
import rego.v1

all_positive if {
    every x in input.xs {
        x > 0
    }
}
"#;
    for mode in RGW_MODES {
        let report = rgw_run(
            policy,
            r#"{"xs": [1, 0, 5]}"#,
            "data.bicep.all_positive",
            rgw_full_standard(mode),
        );
        let rule = rgw_rule(&report, "data.bicep.all_positive");
        let witnesses = rgw_witnesses(&rule["definitions"][0]["conditions"]);
        assert_eq!(witnesses.len(), 1, "{mode:?}: {rule:#}");
        // Two iterations ran (1 passed, 0 failed); the third never started.
        assert_eq!(witnesses[0]["total_iterations"], 2, "{mode:?}");
        assert_eq!(witnesses[0]["success_count"], 1, "{mode:?}");
    }
}

#[test]
fn rgr2_keyless_every_over_an_object_redacts_by_key() {
    let policy = r#"package w
import rego.v1

allow if {
    every v in input.config {
        v != ""
    }
}
"#;
    let input = r#"{"config": {"password": "hunter2"}}"#;
    let report_for = |value_mode| {
        rgw_run(
            policy,
            input,
            "data.w.allow",
            rgw_settings(
                evaluation_trace::ConditionMode::PrimaryOnly,
                evaluation_trace::ExplanationDetail::Standard,
                value_mode,
            ),
        )
    };
    let full = report_for(evaluation_trace::ValueMode::Full);
    let full_witness =
        rgw_witnesses(&rgw_rule(&full, "data.w.allow")["definitions"][0]["conditions"])[0].clone();
    // The key is bound, so the sample names it.
    assert_eq!(full_witness["sample_key"], "password", "{full:#}");
    assert_eq!(full_witness["sample_value"], "hunter2");

    let redacted = report_for(evaluation_trace::ValueMode::Redacted);
    assert!(!redacted.to_string().contains("hunter2"), "{redacted:#}");
    let witness =
        rgw_witnesses(&rgw_rule(&redacted, "data.w.allow")["definitions"][0]["conditions"])[0]
            .clone();
    assert_eq!(witness["sample_key"], "password");
    assert_eq!(witness["sample_value"], "<redacted>");
}

const RGR2_ASSUMPTION_POLICY: &str = r#"package p
import rego.v1

deny contains "v" if {
    input.context.expected == input.password
}
"#;

fn rgr2_assumption_settings(
    value_mode: evaluation_trace::ValueMode,
    eval_mode: evaluation_trace::EvaluationMode,
) -> evaluation_trace::ExplanationSettings {
    evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode,
        condition_mode: evaluation_trace::ConditionMode::AllContributing,
        detail: evaluation_trace::ExplanationDetail::Full,
        assume_unknown_input: true,
        eval_mode,
        unknowns: vec!["input.context".into()],
        ..Default::default()
    }
}

fn rgr2_traced(settings: evaluation_trace::ExplanationSettings) -> (Value, rvm::RegoVM) {
    let mut engine = Engine::new();
    engine
        .add_policy("p.rego".into(), RGR2_ASSUMPTION_POLICY.into())
        .unwrap();
    let compiled = engine
        .compile_with_entrypoint(&Rc::from("data.p.deny"))
        .unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &["data.p.deny"])
            .unwrap();
    let mut vm = rvm::RegoVM::new_with_policy(compiled);
    vm.load_program(program);
    vm.set_explanation_settings(settings);
    vm.set_input(Value::from_json_str(r#"{"password": "hunter2"}"#).unwrap());
    let result = vm.execute_entry_point_by_name("data.p.deny").unwrap();
    (result, vm)
}

#[test]
fn rgr2_causality_assumptions_are_redacted() {
    use evaluation_trace::{EvaluationMode::Causality, ValueMode};
    for (value_mode, expected) in [
        (ValueMode::Full, serde_json::json!("hunter2")),
        (ValueMode::Redacted, serde_json::json!("<redacted>")),
    ] {
        let (result, mut vm) = rgr2_traced(rgr2_assumption_settings(value_mode, Causality));
        let report: serde_json::Value =
            serde_json::from_str(&vm.take_causality_report(result).unwrap()).unwrap();
        let assumptions = report["assumptions"].as_array().expect("assumptions");
        assert_eq!(assumptions.len(), 1, "{report:#}");
        assert_eq!(assumptions[0]["input_path"], "input.context.expected");
        assert_eq!(assumptions[0]["assumed_value"], expected, "{value_mode:?}");
        if value_mode == ValueMode::Redacted {
            assert!(!report.to_string().contains("hunter2"), "{report:#}");
        }
    }
}

#[test]
fn rgr2_partial_evaluation_residuals_keep_their_values() {
    // A residual's value is part of the computed answer (the condition the
    // unknown input must meet), so it is not redacted in any value mode.
    let (result, mut vm) = rgr2_traced(rgr2_assumption_settings(
        evaluation_trace::ValueMode::Redacted,
        evaluation_trace::EvaluationMode::PartialEval,
    ));
    let pe: serde_json::Value =
        serde_json::from_str(&vm.take_partial_eval_result(result).unwrap()).unwrap();
    let text = pe.to_string();
    assert!(text.contains("\"value\":\"hunter2\""), "{pe:#}");
}

#[test]
fn rgr2_common_arm_secret_shapes_are_redacted() {
    let policy = r#"package p
import rego.v1

deny contains r.name if {
    some r in input.resources
    r.type == "x"
}
"#;
    let input = r#"{"resources": [{"name": "a", "type": "x", "properties": {
        "connectionString": "cs-1",
        "secureValue": "sv-1",
        "protectedSettings": {"script": "ps-1"},
        "accountKey": "ak-1",
        "sharedKey": "sk-1",
        "passphrase": "pp-1",
        "pwd": "pw-1",
        "private-key": "pk-1",
        "api key": "api-1",
        "appSettings": [
            {"name": "DB_PASSWORD", "value": "dbp-1"},
            {"name": "MODE", "value": "keep-1"}
        ],
        "mode": "basic"
    }}]}"#;
    let secrets = [
        "cs-1", "sv-1", "ps-1", "ak-1", "sk-1", "pp-1", "pw-1", "pk-1", "api-1", "dbp-1",
    ];
    for mode in RGW_MODES {
        let full = rgw_run(policy, input, "data.p.deny", rgw_full_standard(mode)).to_string();
        for secret in secrets.iter().chain(&["keep-1", "basic"]) {
            assert!(full.contains(secret), "{mode:?}: Full must show {secret}");
        }
        let redacted = rgw_run(
            policy,
            input,
            "data.p.deny",
            rgw_settings(
                mode,
                evaluation_trace::ExplanationDetail::Standard,
                evaluation_trace::ValueMode::Redacted,
            ),
        )
        .to_string();
        for secret in secrets {
            assert!(
                !redacted.contains(secret),
                "{mode:?}: {secret} leaked: {redacted}"
            );
        }
        // Not secrets: a pair whose name is not sensitive, and plain fields.
        assert!(redacted.contains("keep-1") && redacted.contains("basic"));
    }
}

#[test]
fn rgr2_helper_rule_results_are_redacted() {
    let policy = r#"package p
import rego.v1

admin_token := input.vault.token

settings := input.settings

deny contains "x" if {
    admin_token != ""
    settings.mode == "on"
}
"#;
    let input = r#"{"vault": {"token": "tok-1"}, "settings": {"mode": "on", "password": "pw-9"}}"#;
    let report_for = |value_mode| {
        rgw_run(
            policy,
            input,
            "data.p.deny",
            rgw_settings(
                evaluation_trace::ConditionMode::PrimaryOnly,
                evaluation_trace::ExplanationDetail::Standard,
                value_mode,
            ),
        )
    };
    let full = report_for(evaluation_trace::ValueMode::Full);
    assert_eq!(rgw_rule(&full, "data.p.admin_token")["result"], "tok-1");
    assert_eq!(
        rgw_rule(&full, "data.p.settings")["result"]["password"],
        "pw-9"
    );

    let redacted = report_for(evaluation_trace::ValueMode::Redacted);
    // A helper named like a secret is hidden whole; others are sanitized.
    assert_eq!(
        rgw_rule(&redacted, "data.p.admin_token")["result"],
        "<redacted>"
    );
    let settings = &rgw_rule(&redacted, "data.p.settings")["result"];
    assert_eq!(settings["password"], "<redacted>");
    assert_eq!(settings["mode"], "on");
    // The entry point's result is the policy output and is unchanged.
    assert_eq!(
        rgw_rule(&redacted, "data.p.deny")["result"],
        serde_json::json!(["x"])
    );
    assert!(!redacted.to_string().contains("tok-1"), "{redacted:#}");
    assert!(!redacted.to_string().contains("pw-9"), "{redacted:#}");
}

// ---------------------------------------------------------------------------
// RG-R2 round 3: provenance-based redaction (pair values, helper results,
// keys under sensitive collections) in both execution modes.
// ---------------------------------------------------------------------------

const RGR3_SECRET: &str = "opaque-42";

/// Run `entry` traced in both execution modes and return both reports.
fn rgr3_reports(
    policy: &str,
    input: &str,
    entry: &str,
    value_mode: evaluation_trace::ValueMode,
) -> Vec<serde_json::Value> {
    rgr3_reports_with(
        policy,
        Value::from_json_str(input).unwrap(),
        entry,
        value_mode,
    )
}

/// `rgr3_reports` for an input JSON cannot express (sets, compound keys).
fn rgr3_reports_with(
    policy: &str,
    input: Value,
    entry: &str,
    value_mode: evaluation_trace::ValueMode,
) -> Vec<serde_json::Value> {
    let mut engine = Engine::new();
    engine
        .add_policy("rgr3.rego".into(), policy.into())
        .unwrap();
    engine.set_input(input.clone());
    let interpreted = engine.eval_rule(entry.into()).unwrap();
    let compiled = engine.compile_with_entrypoint(&Rc::from(entry)).unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entry]).unwrap();
    [
        rvm::vm::ExecutionMode::RunToCompletion,
        rvm::vm::ExecutionMode::Suspendable,
    ]
    .into_iter()
    .map(|execution_mode| {
        let mut vm = rvm::RegoVM::new_with_policy(compiled.clone());
        vm.load_program(program.clone());
        vm.set_execution_mode(execution_mode);
        vm.set_max_instructions(10_000_000);
        vm.set_explanation_settings(evaluation_trace::ExplanationSettings {
            enabled: true,
            value_mode,
            condition_mode: evaluation_trace::ConditionMode::AllContributing,
            detail: evaluation_trace::ExplanationDetail::Full,
            ..Default::default()
        });
        vm.set_input(input.clone());
        let result = vm.execute_entry_point_by_name(entry).unwrap();
        assert_eq!(result, interpreted, "{execution_mode:?}");
        serde_json::from_str(&vm.take_causality_report(result).unwrap()).unwrap()
    })
    .collect()
}

/// Assert Redacted hides `secret` in both modes while Full shows it, and that
/// `kept` (a non-secret control) survives Redacted.
fn rgr3_assert_hidden(policy: &str, input: &str, entry: &str, secret: &str, kept: &str) {
    use evaluation_trace::ValueMode;
    for report in rgr3_reports(policy, input, entry, ValueMode::Full) {
        assert!(
            report.to_string().contains(secret),
            "Full control: {report:#}"
        );
    }
    for report in rgr3_reports(policy, input, entry, ValueMode::Redacted) {
        let text = report.to_string();
        assert!(
            !text.contains(secret),
            "Redacted leaks {secret}: {report:#}"
        );
        assert!(text.contains(kept), "Redacted lost {kept}: {report:#}");
    }
}

#[test]
fn rgr3_extracted_pair_value_is_redacted() {
    let input = r#"{"appSettings": [
        {"name": "DB_PASSWORD", "value": "opaque-42"},
        {"name": "REGION", "value": "westus-kept"}]}"#;
    // Comparison on the extracted value, and a builtin over it.
    for policy in [
        r#"package p
import rego.v1
deny contains s.name if {
    some s in input.appSettings
    s.value != ""
}
"#,
        r#"package p
import rego.v1
deny contains s.name if {
    some s in input.appSettings
    not startswith(s.value, "@Microsoft.KeyVault(")
}
"#,
    ] {
        rgr3_assert_hidden(policy, input, "data.p.deny", RGR3_SECRET, "westus-kept");
    }
}

#[test]
fn rgr3_pair_value_read_by_a_dynamic_key_or_a_literal_chain_is_redacted() {
    let input = r#"{"field": "value", "appSettings": [
        {"name": "DB_PASSWORD", "value": "opaque-42"},
        {"name": "REGION", "value": "westus-kept"}]}"#;
    for policy in [
        // `Index` with a key computed at runtime.
        r#"package p
import rego.v1
deny contains s.name if {
    some s in input.appSettings
    s[input.field] != ""
}
"#,
        // `ChainedIndex` through a literal path from `input`.
        r#"package p
import rego.v1
deny contains "db" if {
    input.appSettings[0].name == "DB_PASSWORD"
    input.appSettings[0].value != ""
    input.appSettings[1].value != ""
}
"#,
    ] {
        rgr3_assert_hidden(policy, input, "data.p.deny", RGR3_SECRET, "westus-kept");
    }
}

#[test]
fn rgr3_pair_value_reached_by_iterating_the_pair_is_redacted() {
    let policy = r#"package p
import rego.v1
deny contains k if {
    some s in input.appSettings
    some k, v in s
    k == "value"
    v != ""
}
"#;
    let input = r#"{"appSettings": [{"name": "DB_PASSWORD", "value": "opaque-42"}]}"#;
    rgr3_assert_hidden(policy, input, "data.p.deny", RGR3_SECRET, "DB_PASSWORD");
}

#[test]
fn rgr3_helper_result_from_a_sensitive_path_is_redacted() {
    let policy = r#"package p
import rego.v1
candidate := input.password
location := input.location
leaked contains input.password if { true }
deny contains "x" if {
    candidate != ""
    location != ""
    count(leaked) > 0
}
"#;
    let input = r#"{"password": "opaque-42", "location": "westus-kept"}"#;
    rgr3_assert_hidden(policy, input, "data.p.deny", RGR3_SECRET, "westus-kept");
}

#[test]
fn rgr3_keys_under_a_sensitive_collection_are_masked_in_provenance() {
    let input = r#"{"tokens": {"opaque-42": true}, "regions": {"westus-kept": true}}"#;
    for policy in [
        r#"package p
import rego.v1
allow if {
    every v in input.tokens { v == true }
    every w in input.regions { w == true }
}
"#,
        r#"package p
import rego.v1
allow if {
    some k, v in input.tokens
    v == true
    some j, w in input.regions
    w == true
}
"#,
    ] {
        rgr3_assert_hidden(policy, input, "data.p.allow", RGR3_SECRET, "westus-kept");
    }
}

#[test]
fn rgr3_rewritten_values_are_marked_redacted() {
    use evaluation_trace::ValueMode;
    let policy = r#"package p
import rego.v1
candidate := input.password
password_auth_enabled if input.authMode == "local"
deny contains "x" if {
    candidate != ""
    password_auth_enabled
}
"#;
    // `password_auth_enabled` is a computed boolean: only its name is
    // sensitive, unlike a value read from a sensitive path.
    let input = r#"{"password": "opaque-42", "authMode": "local"}"#;
    for report in rgr3_reports(policy, input, "data.p.deny", ValueMode::Redacted) {
        let candidate = rgw_rule(&report, "data.p.candidate");
        assert_eq!(candidate["result"], "<redacted>", "{report:#}");
        assert_eq!(candidate["redacted"], true, "{report:#}");
        // A boolean result under a sensitive name is not a secret.
        let flag = rgw_rule(&report, "data.p.password_auth_enabled");
        assert_eq!(flag["result"], true, "{report:#}");
        assert!(flag.get("redacted").is_none(), "{report:#}");
        assert!(
            rgw_rule(&report, "data.p.deny").get("redacted").is_none(),
            "{report:#}"
        );
    }
    for report in rgr3_reports(policy, input, "data.p.deny", ValueMode::Full) {
        assert!(rgw_rule(&report, "data.p.candidate")
            .get("redacted")
            .is_none());
    }
}

#[test]
fn rgr3_redacted_assumptions_are_marked() {
    use evaluation_trace::{EvaluationMode::Causality, ValueMode};
    for (value_mode, marked) in [(ValueMode::Full, false), (ValueMode::Redacted, true)] {
        let (result, mut vm) = rgr2_traced(rgr2_assumption_settings(value_mode, Causality));
        let report: serde_json::Value =
            serde_json::from_str(&vm.take_causality_report(result).unwrap()).unwrap();
        let assumption = &report["assumptions"][0];
        assert_eq!(
            assumption.get("redacted").is_some_and(|v| v == true),
            marked,
            "{value_mode:?}: {report:#}"
        );
    }
}

#[test]
fn rgr3_both_execution_modes_report_the_same_provenance() {
    // Helper rules (called twice, so the second call would hit the rule cache),
    // a function with an argument, a nested call and a default.
    let policy = r#"package p
import rego.v1
default fallback := "none"
fallback := input.missing
region := input.resources[0].location
is_east(loc) if startswith(loc, "east")
name_of(r) := n if { n := r.name }
deny contains n if {
    some r in input.resources
    region != ""
    region != "x"
    is_east(r.location)
    n := name_of(r)
    fallback == "none"
}
"#;
    let input = r#"{"resources": [{"name": "a", "location": "eastus"},
                                 {"name": "b", "location": "westus"}]}"#;
    let reports = rgr3_reports(
        policy,
        input,
        "data.p.deny",
        evaluation_trace::ValueMode::Full,
    );
    assert_eq!(reports.len(), 2);
    // Suspendable records one definition outcome per (rule, definition) for
    // the whole trace while run-to-completion records one per call, so helper
    // `definitions` are compared by provenance only; everything else is equal.
    let normalized = |report: &serde_json::Value| {
        let mut report = report.clone();
        for rule in report["rules"].as_array_mut().unwrap() {
            if rule["name"] != "data.p.deny" {
                rule.as_object_mut().unwrap().remove("definitions");
            }
        }
        report
    };
    fn provenances(value: &serde_json::Value, out: &mut Vec<String>) {
        match value {
            serde_json::Value::Object(map) => {
                for (key, item) in map {
                    if key == "provenance" {
                        out.push(item.to_string());
                    }
                    provenances(item, out);
                }
            }
            serde_json::Value::Array(items) => items.iter().for_each(|i| provenances(i, out)),
            _ => {}
        }
    }
    let sorted_provenances = |report: &serde_json::Value| {
        let mut out = Vec::new();
        provenances(report, &mut out);
        out.sort();
        out.dedup();
        out
    };
    assert_eq!(normalized(&reports[0]), normalized(&reports[1]));
    assert_eq!(
        sorted_provenances(&reports[0]),
        sorted_provenances(&reports[1])
    );
    // Non-vacuous: helper-derived operands carry their source paths.
    assert!(
        sorted_provenances(&reports[1]).contains(&"\"input.resources[0].location\"".to_string()),
        "{:#}",
        reports[1]
    );
}

#[test]
fn rgr3_a_run_stopped_inside_a_rule_leaves_no_provenance_behind() {
    let policy = r#"package p
import rego.v1
helper := input.password
deny contains "x" if {
    helper != ""
    count([i | some i in numbers.range(1, 50)]) > 0
}
"#;
    let entry = "data.p.deny";
    let input = Value::from_json_str(r#"{"password": "opaque-42"}"#).unwrap();
    let mut engine = Engine::new();
    engine.add_policy("p.rego".into(), policy.into()).unwrap();
    let compiled = engine.compile_with_entrypoint(&Rc::from(entry)).unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entry]).unwrap();
    let settings = evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode: evaluation_trace::ValueMode::Full,
        condition_mode: evaluation_trace::ConditionMode::AllContributing,
        detail: evaluation_trace::ExplanationDetail::Full,
        ..Default::default()
    };
    for execution_mode in [
        rvm::vm::ExecutionMode::RunToCompletion,
        rvm::vm::ExecutionMode::Suspendable,
    ] {
        let report_of = |vm: &mut rvm::RegoVM| {
            let result = vm.execute_entry_point_by_name(entry).unwrap();
            serde_json::from_str::<serde_json::Value>(&vm.take_causality_report(result).unwrap())
                .unwrap()
        };
        let mut fresh = rvm::RegoVM::new_with_policy(compiled.clone());
        fresh.load_program(program.clone());
        fresh.set_execution_mode(execution_mode);
        fresh.set_explanation_settings(settings.clone());
        fresh.set_input(input.clone());
        let expected = report_of(&mut fresh);

        let mut reused = rvm::RegoVM::new_with_policy(compiled.clone());
        reused.load_program(program.clone());
        reused.set_execution_mode(execution_mode);
        reused.set_explanation_settings(settings.clone());
        reused.set_input(input.clone());
        reused.set_max_instructions(40);
        assert!(
            reused.execute_entry_point_by_name(entry).is_err(),
            "{execution_mode:?}: the limit must stop the first run"
        );
        // Discard the failed run's trace, as a caller must; this test is about
        // register provenance, which no caller can reset.
        reused.take_causality_report(Value::Undefined).unwrap();
        reused.set_max_instructions(1_000_000);
        reused.set_explanation_settings(settings.clone());
        assert_eq!(report_of(&mut reused), expected, "{execution_mode:?}");
    }
}

// ---------------------------------------------------------------------------
// RG-R2 round 4: displayed values and their sensitivity come from the same
// evaluation; paths the VM writes are all understood.
// ---------------------------------------------------------------------------

#[test]
fn rgr4_function_called_twice_keeps_the_sensitive_result_hidden() {
    let policy = r#"package p
import rego.v1
candidate(x) := x if x != "skip"
allow if {
    candidate(input.password) != ""
    candidate(input.public) != ""
}
"#;
    let input = r#"{"password": "opaque-42", "public": "skip"}"#;
    rgr3_assert_hidden(policy, input, "data.p.allow", RGR3_SECRET, "skip");
}

#[test]
fn rgr4_multi_definition_rule_keeps_its_value_provenance() {
    let policy = r#"package p
import rego.v1
candidate := input.password if input.first
candidate := input.public if input.second
allow if {
    candidate != ""
    input.region != ""
}
"#;
    let input = r#"{"password": "opaque-42", "public": "w", "first": true, "second": false, "region": "westus-kept"}"#;
    rgr3_assert_hidden(policy, input, "data.p.allow", RGR3_SECRET, "westus-kept");
}

#[test]
fn rgr4_pair_under_a_non_identifier_field_is_redacted() {
    let policy = r#"package p
import rego.v1
allow if {
    s := input["app-settings"]
    s.value != ""
    input.region != ""
}
"#;
    let input = r#"{"app-settings": {"name": "DB_PASSWORD", "value": "opaque-42"},
                    "region": "westus-kept"}"#;
    rgr3_assert_hidden(policy, input, "data.p.allow", RGR3_SECRET, "westus-kept");
}

#[test]
fn rgr4_witness_over_a_pair_object_is_redacted() {
    let policy = r#"package p
import rego.v1
allow if {
    some k, v in input.setting
    k == "value"
    v != ""
    input.region != ""
}
"#;
    let input = r#"{"setting": {"name": "DB_PASSWORD", "value": "opaque-42"},
                    "region": "westus-kept"}"#;
    rgr3_assert_hidden(policy, input, "data.p.allow", RGR3_SECRET, "westus-kept");
}

#[test]
fn rgr4_helpers_returning_sensitive_keys_are_redacted() {
    let policy = r#"package p
import rego.v1
candidate := k if {
    some k, v in input.tokens
    v == true
}
names := {k | some k, _ in input.tokens}
flags[k] := 1 if some k, _ in input.tokens
allow if {
    candidate != ""
    count(names) > 0
    count(flags) > 0
    input.region != ""
}
"#;
    let input = r#"{"tokens": {"opaque-42": true}, "region": "westus-kept"}"#;
    rgr3_assert_hidden(policy, input, "data.p.allow", RGR3_SECRET, "westus-kept");
}

#[test]
fn rgr4_keys_iterated_across_a_pair_path_overflow_stay_hidden() {
    // 1,024 pair values fill the record exactly; the 1,025th, read inside the
    // first iteration over `input.cfg.value`, overflows it. The loop's second
    // key must stay hidden under the overflow rules.
    let policy = r#"package p
import rego.v1
allow if {
    count([s.value | some s in input.pairs]) > 0
    some k, v in input.cfg.value
    input.extra.value != ""
    k != "a-first"
    v > 0
}
"#;
    let pairs: Vec<String> = (0..1024)
        .map(|i| format!(r#"{{"name": "DB_PASSWORD", "value": "v{i}"}}"#))
        .collect();
    let input = format!(
        r#"{{"cfg": {{"value": {{"a-first": 1, "opaque-42": 2}}}},
             "extra": {{"name": "API_TOKEN", "value": "t"}},
             "pairs": [{}]}}"#,
        pairs.join(",")
    );
    for report in rgr3_reports(
        policy,
        &input,
        "data.p.allow",
        evaluation_trace::ValueMode::Redacted,
    ) {
        assert!(!report.to_string().contains(RGR3_SECRET), "{report:#}");
    }
    for report in rgr3_reports(
        policy,
        &input,
        "data.p.allow",
        evaluation_trace::ValueMode::Full,
    ) {
        assert!(report.to_string().contains(RGR3_SECRET), "Full control");
    }
}

#[test]
fn rgr4_multi_value_object_helpers_are_redacted() {
    // `bag[k] contains v` compiles to `ObjectDeepSet`, which records no
    // emission; its leaves are recorded separately for redaction.
    let policy = r#"package p
import rego.v1
bag[k] contains input.password if k := "a"
bag[k] contains input.public if k := "b"
plain[k] contains input.region if k := "b"
allow if {
    count(bag) > 0
    count(plain) > 0
}
"#;
    // `public` nests the same secret one level down inside the set.
    let input = r#"{"password": "opaque-42", "public": ["opaque-42"], "region": "westus-kept"}"#;
    rgr3_assert_hidden(policy, input, "data.p.allow", RGR3_SECRET, "westus-kept");
    // A head with several keys also writes through `ObjectDeepSet`, nesting
    // the leaf deeper.
    let nested = r#"package p
import rego.v1
deep[a][b] contains input.password if {
    a := "x"
    b := "y"
}
allow if {
    count(deep) > 0
    input.region != ""
}
"#;
    rgr3_assert_hidden(nested, input, "data.p.allow", RGR3_SECRET, "westus-kept");
}

#[test]
fn rgr4_set_elements_at_a_sensitive_path_are_hidden_as_keys() {
    use evaluation_trace::ValueMode;
    let policy = r#"package p
import rego.v1
allow if {
    some k, _ in input.apiTokens
    k != ""
    input.region != ""
}
"#;
    // `apiTokens` must be a set, which JSON cannot express.
    let mut input = Value::from_json_str(r#"{"apiTokens": [], "region": "westus-kept"}"#).unwrap();
    let tokens: std::collections::BTreeSet<Value> =
        [Value::from(RGR3_SECRET)].into_iter().collect();
    input
        .as_object_mut()
        .unwrap()
        .insert(Value::from("apiTokens"), Value::from(tokens));
    for report in rgr3_reports_with(policy, input.clone(), "data.p.allow", ValueMode::Full) {
        assert!(report.to_string().contains(RGR3_SECRET), "Full control");
    }
    for report in rgr3_reports_with(policy, input, "data.p.allow", ValueMode::Redacted) {
        let text = report.to_string();
        assert!(!text.contains(RGR3_SECRET), "{report:#}");
        assert!(text.contains("westus-kept"), "{report:#}");
    }
}

// ---------------------------------------------------------------------------
// RG-12: an outer helper-call condition takes a failed inner condition's
// provenance only when the helper returned falsy.
// ---------------------------------------------------------------------------

/// `left.provenance` of every reported condition with exactly `text`, in
/// report order, across rules, definitions and emissions.
fn rg12_left_provenances(report: &serde_json::Value, text: &str) -> Vec<Option<String>> {
    fn walk(value: &serde_json::Value, text: &str, out: &mut Vec<Option<String>>) {
        match value {
            serde_json::Value::Object(map) => {
                if map.get("text").and_then(|t| t.as_str()) == Some(text)
                    && map.contains_key("outcome")
                {
                    out.push(
                        map.get("left")
                            .and_then(|l| l.get("provenance"))
                            .and_then(|p| p.as_str())
                            .map(str::to_string),
                    );
                }
                for (key, item) in map {
                    if key != "helper_conditions" {
                        walk(item, text, out);
                    }
                }
            }
            serde_json::Value::Array(items) => items.iter().for_each(|item| walk(item, text, out)),
            _ => {}
        }
    }
    let mut out = Vec::new();
    walk(report, text, &mut out);
    out
}

const RG12_TWO_DEFINITIONS: &str = r#"package p
import rego.v1
_ok(r) if r.a.x == "yes"
_ok(r) if r.b == "yes"
"#;

/// Reports for `deny` in both execution modes (Full values), with the outer
/// condition's provenances. Panics if the condition is never reported.
fn rg12_outer(policy: &str, input: &str, text: &str) -> Vec<Vec<Option<String>>> {
    rgr3_reports(
        policy,
        input,
        "data.p.deny",
        evaluation_trace::ValueMode::Full,
    )
    .iter()
    .map(|report| {
        let found = rg12_left_provenances(report, text);
        assert!(!found.is_empty(), "{text} not reported: {report:#}");
        found
    })
    .collect()
}

#[test]
fn rg12_succeeding_helper_does_not_borrow_a_failed_definition_path() {
    let policy = format!(
        "{RG12_TWO_DEFINITIONS}deny contains r.name if {{\n    some r in input.resources\n    _ok(r)\n}}\n"
    );
    let input = r#"{"resources": [{"name": "n", "a": {"x": "no"}, "b": "yes"}]}"#;
    for provenances in rg12_outer(&policy, input, "_ok(r)") {
        for provenance in provenances {
            assert!(
                !provenance.as_deref().unwrap_or("").contains(".a.x"),
                "a succeeding helper took its failed definition's path: {provenance:?}"
            );
        }
    }
}

#[test]
fn rg12_succeeding_helper_does_not_borrow_a_failed_iteration_path() {
    let policy = r#"package p
import rego.v1
_has_ok(r) if {
    some e in r.items
    e.ok == true
}
deny contains r.name if {
    some r in input.resources
    _has_ok(r)
}
"#;
    let input = r#"{"resources": [{"name": "n", "items": [{"ok": false}, {"ok": true}]}]}"#;
    for provenances in rg12_outer(policy, input, "_has_ok(r)") {
        for provenance in provenances {
            assert!(
                !provenance.as_deref().unwrap_or("").contains("items[0]"),
                "a succeeding helper took its failed iteration's path: {provenance:?}"
            );
        }
    }
}

#[test]
fn rg12_negated_helper_that_held_does_not_borrow_a_failed_path() {
    let policy = format!(
        "{RG12_TWO_DEFINITIONS}deny contains r.name if {{\n    some r in input.resources\n    not _ok(r)\n}}\n"
    );
    let input = r#"{"resources": [{"name": "n", "a": {"x": "no"}, "b": "yes"}]}"#;
    for provenances in rg12_outer(&policy, input, "not _ok(r)") {
        for provenance in provenances {
            assert!(
                !provenance.as_deref().unwrap_or("").contains(".a.x"),
                "`not` over a helper that held took a failed path: {provenance:?}"
            );
        }
    }
}

#[test]
fn rg12_falsy_helper_still_derives_its_failed_path() {
    // Controls: a helper that returned falsy keeps the derived provenance,
    // directly and behind `not`.
    let input = r#"{"resources": [{"name": "n", "a": {"x": "no"}, "b": "no"}]}"#;
    let direct = format!(
        "{RG12_TWO_DEFINITIONS}deny contains r.name if {{\n    some r in input.resources\n    _ok(r)\n}}\n"
    );
    for provenances in rg12_outer(&direct, input, "_ok(r)") {
        assert!(
            provenances
                .iter()
                .any(|p| p.as_deref() == Some("input.resources[0].b")),
            "{provenances:?}"
        );
    }
    let negated = format!(
        "{RG12_TWO_DEFINITIONS}deny contains r.name if {{\n    some r in input.resources\n    not _ok(r)\n}}\n"
    );
    for provenances in rg12_outer(&negated, input, "not _ok(r)") {
        assert!(
            provenances
                .iter()
                .any(|p| p.as_deref() == Some("input.resources[0].b")),
            "{provenances:?}"
        );
    }
}

/// Causality report for `deny` in partial-evaluation mode with `unknowns`,
/// in both execution modes, with the outer condition's provenances.
fn rg12_outer_pe(
    policy: &str,
    input: &str,
    text: &str,
    unknowns: &[&str],
) -> Vec<Vec<Option<String>>> {
    let entry = "data.p.deny";
    let mut engine = Engine::new();
    engine
        .add_policy("rg12.rego".into(), policy.into())
        .unwrap();
    let compiled = engine.compile_with_entrypoint(&Rc::from(entry)).unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entry]).unwrap();
    [
        rvm::vm::ExecutionMode::RunToCompletion,
        rvm::vm::ExecutionMode::Suspendable,
    ]
    .into_iter()
    .map(|execution_mode| {
        let mut vm = rvm::RegoVM::new_with_policy(compiled.clone());
        vm.load_program(program.clone());
        vm.set_execution_mode(execution_mode);
        vm.set_explanation_settings(evaluation_trace::ExplanationSettings {
            enabled: true,
            value_mode: evaluation_trace::ValueMode::Full,
            condition_mode: evaluation_trace::ConditionMode::AllContributing,
            detail: evaluation_trace::ExplanationDetail::Full,
            assume_unknown_input: true,
            eval_mode: evaluation_trace::EvaluationMode::PartialEval,
            unknowns: unknowns.iter().map(|u| (*u).into()).collect(),
            ..Default::default()
        });
        vm.set_input(Value::from_json_str(input).unwrap());
        let result = vm.execute_entry_point_by_name(entry).unwrap();
        let report: serde_json::Value =
            serde_json::from_str(&vm.take_causality_report(result).unwrap()).unwrap();
        let found = rg12_left_provenances(&report, text);
        assert!(
            !found.is_empty(),
            "{text} not reported ({execution_mode:?}): {report:#}"
        );
        found
    })
    .collect()
}

#[test]
fn rg12_negated_helper_held_by_an_assumption_does_not_borrow_a_failed_path() {
    // In partial evaluation `not` turns an assumption-dependent `true` into
    // `true`, so the outer guard succeeds although the helper held (assumed).
    let policy = format!(
        "{RG12_TWO_DEFINITIONS}deny contains r.name if {{\n    some r in input.resources\n    not _ok(r)\n}}\n"
    );
    let input = r#"{"resources": [{"name": "n", "a": {"x": "no"}}]}"#;
    for provenances in rg12_outer_pe(&policy, input, "not _ok(r)", &["input.resources[0].b"]) {
        for provenance in provenances {
            assert!(
                !provenance.as_deref().unwrap_or("").contains(".a.x"),
                "a helper held by an assumption took a failed path: {provenance:?}"
            );
        }
    }
    // Control: in the same mode, a helper that is concretely falsy (no
    // unknown reached) still derives its last failed path.
    let falsy = r#"{"resources": [{"name": "n", "a": {"x": "no"}, "b": "no"}]}"#;
    for provenances in rg12_outer_pe(&policy, falsy, "not _ok(r)", &["input.other"]) {
        assert!(
            provenances
                .iter()
                .any(|p| p.as_deref() == Some("input.resources[0].b")),
            "{provenances:?}"
        );
    }
}

#[test]
fn rg12_assumption_in_a_nested_or_cut_helper_is_not_definite() {
    // The assumption sits one helper deeper (`_ok` -> `_inner`).
    let nested = r#"package p
import rego.v1
_ok(r) if r.a.x == "yes"
_ok(r) if _inner(r)
_inner(r) if r.b == "yes"
deny contains r.name if {
    some r in input.resources
    not _ok(r)
}
"#;
    let input = r#"{"resources": [{"name": "n", "a": {"x": "no"}}]}"#;
    for provenances in rg12_outer_pe(nested, input, "not _ok(r)", &["input.resources[0].b"]) {
        for provenance in provenances {
            assert!(
                !provenance.as_deref().unwrap_or("").contains(".a.x"),
                "nested assumption: {provenance:?}"
            );
        }
    }
    // The assumption sits below the helper depth cap, so it is never
    // reported; the cut expansion must count as possibly assumed.
    let mut deep =
        String::from("package p\nimport rego.v1\n_ok(r) if r.a.x == \"yes\"\n_ok(r) if _h1(r)\n");
    for level in 1..=10 {
        deep.push_str(&format!("_h{level}(r) if _h{}(r)\n", level + 1));
    }
    deep.push_str("_h11(r) if r.b == \"yes\"\n");
    deep.push_str("deny contains r.name if {\n    some r in input.resources\n    not _ok(r)\n}\n");
    for provenances in rg12_outer_pe(&deep, input, "not _ok(r)", &["input.resources[0].b"]) {
        for provenance in provenances {
            assert!(
                !provenance.as_deref().unwrap_or("").contains(".a.x"),
                "assumption below the depth cap: {provenance:?}"
            );
        }
    }
}

#[test]
fn rg12_assumption_hidden_from_reported_conditions_is_not_definite() {
    let input = r#"{"resources": [{"name": "n", "a": {"x": "no"}}]}"#;
    // The nested call is wrapped in a comparison, so it is not expanded as a
    // helper, and its assumption never appears among `_ok`'s conditions.
    let wrapped = r#"package p
import rego.v1
_ok(r) if r.a.x == "yes"
_ok(r) if _inner(r) == true
_inner(r) if r.b == "yes"
deny contains r.name if {
    some r in input.resources
    not _ok(r)
}
"#;
    // `not r.b` over an unknown records its assumption only in the trace's
    // assumptions; the guard itself reports success.
    let negation = r#"package p
import rego.v1
_ok(r) if r.a.x == "yes"
_ok(r) if not r.b
deny contains r.name if {
    some r in input.resources
    not _ok(r)
}
"#;
    for (name, policy) in [("wrapped", wrapped), ("negation", negation)] {
        for provenances in rg12_outer_pe(policy, input, "not _ok(r)", &["input.resources[0].b"]) {
            for provenance in provenances {
                assert!(
                    !provenance.as_deref().unwrap_or("").contains(".a.x"),
                    "{name}: a helper held by a hidden assumption took a failed path: {provenance:?}"
                );
            }
        }
    }
}

#[test]
fn rg12_each_call_uses_its_own_assumption_status() {
    // r0's helper held by an assumption (its `b` is unknown); r1's helper is
    // concretely falsy. Each outer condition must use its own call.
    let policy = format!(
        "{RG12_TWO_DEFINITIONS}deny contains r.name if {{\n    some r in input.resources\n    not _ok(r)\n}}\n"
    );
    let input = r#"{"resources": [{"name": "r0", "a": {"x": "no"}},
                                 {"name": "r1", "a": {"x": "no"}, "b": "no"}]}"#;
    for provenances in rg12_outer_pe(&policy, input, "not _ok(r)", &["input.resources[0].b"]) {
        assert!(
            provenances
                .iter()
                .all(|p| !p.as_deref().unwrap_or("").contains("resources[0].a.x")),
            "r0 took a failed path: {provenances:?}"
        );
        assert!(
            provenances
                .iter()
                .any(|p| p.as_deref() == Some("input.resources[1].b")),
            "r1 lost its derived path: {provenances:?}"
        );
    }
}

#[test]
fn suspendable_partial_evaluation_negates_assumption_dependent_helpers() {
    // `not` over a helper that held only by an assumption is indeterminate in
    // partial evaluation, so the negation is assumed to hold. Both execution
    // modes must agree (regression in 6d351052, which stopped suspendable
    // calls from leaking callee provenance and exposed the missing counter).
    let policy = format!(
        "{RG12_TWO_DEFINITIONS}deny contains r.name if {{\n    some r in input.resources\n    not _ok(r)\n}}\n"
    );
    let entry = "data.p.deny";
    let run = |input: &str, execution_mode| {
        let mut engine = Engine::new();
        engine.add_policy("p.rego".into(), policy.clone()).unwrap();
        let compiled = engine.compile_with_entrypoint(&Rc::from(entry)).unwrap();
        let program =
            languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entry]).unwrap();
        let mut vm = rvm::RegoVM::new_with_policy(compiled);
        vm.load_program(program);
        vm.set_execution_mode(execution_mode);
        vm.set_explanation_settings(evaluation_trace::ExplanationSettings {
            enabled: true,
            assume_unknown_input: true,
            eval_mode: evaluation_trace::EvaluationMode::PartialEval,
            unknowns: vec!["input.resources[0].b".into()],
            ..Default::default()
        });
        vm.set_input(Value::from_json_str(input).unwrap());
        vm.execute_entry_point_by_name(entry).unwrap()
    };
    let names = |names: &[&str]| {
        Value::from(
            names
                .iter()
                .map(|n| Value::from(*n))
                .collect::<std::collections::BTreeSet<Value>>(),
        )
    };
    for (input, expected) in [
        // Held by an assumption: indeterminate, so `not` is assumed to hold.
        (
            r#"{"resources": [{"name": "n", "a": {"x": "no"}}]}"#,
            names(&["n"]),
        ),
        // Controls: concretely falsy, and concretely true.
        (
            r#"{"resources": [{"name": "n", "a": {"x": "no"}, "b": "no"}]}"#,
            names(&["n"]),
        ),
        (
            r#"{"resources": [{"name": "n", "a": {"x": "yes"}, "b": "no"}]}"#,
            names(&[]),
        ),
    ] {
        for execution_mode in [
            rvm::vm::ExecutionMode::RunToCompletion,
            rvm::vm::ExecutionMode::Suspendable,
        ] {
            assert_eq!(
                run(input, execution_mode),
                expected,
                "{execution_mode:?} {input}"
            );
        }
    }
}

#[test]
fn rgp3_assumption_counter_leaks_into_an_unrelated_negation() {
    // KNOWN DEFECT (RG-P3), pinned so a fix is noticed. Partial evaluation
    // tracks assumption dependence with one VM-wide counter, so a helper that
    // held only by an assumption and was consumed positively makes a later
    // `not` over a concretely true helper hold. The correct answer for both
    // cases is the empty set; both execution modes currently over-approximate.
    let cases = [
        (
            "package p\nimport rego.v1\n_a(r) if r.u == 1\n_b(r) if r.k == 1\ndeny contains r.name if {\n    some r in input.resources\n    _a(r)\n    not _b(r)\n}\n",
            r#"{"resources": [{"name": "n", "k": 1}]}"#,
            "input.resources[0].u",
            "n",
        ),
        (
            "package p\nimport rego.v1\n_pending(r) if r.b == \"yes\"\n_known(unused, r) if r.a == \"yes\"\ndeny contains \"bad\" if {\n    v := _pending(input)\n    not _known(v, input)\n}\n",
            r#"{"a": "yes"}"#,
            "input.b",
            "bad",
        ),
    ];
    let entry = "data.p.deny";
    for (policy, input, unknown, leaked) in cases {
        for execution_mode in [
            rvm::vm::ExecutionMode::RunToCompletion,
            rvm::vm::ExecutionMode::Suspendable,
        ] {
            let mut engine = Engine::new();
            engine.add_policy("p.rego".into(), policy.into()).unwrap();
            let compiled = engine.compile_with_entrypoint(&Rc::from(entry)).unwrap();
            let program =
                languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entry])
                    .unwrap();
            let mut vm = rvm::RegoVM::new_with_policy(compiled);
            vm.load_program(program);
            vm.set_execution_mode(execution_mode);
            vm.set_explanation_settings(evaluation_trace::ExplanationSettings {
                enabled: true,
                assume_unknown_input: true,
                eval_mode: evaluation_trace::EvaluationMode::PartialEval,
                unknowns: vec![unknown.into()],
                ..Default::default()
            });
            vm.set_input(Value::from_json_str(input).unwrap());
            let expected = Value::from(
                [Value::from(leaked)]
                    .into_iter()
                    .collect::<std::collections::BTreeSet<Value>>(),
            );
            assert_eq!(
                vm.execute_entry_point_by_name(entry).unwrap(),
                expected,
                "{execution_mode:?} {input}"
            );
        }
    }
}

/// Run `data.t.deny` with causality explanations, in causality mode or in
/// partial-evaluation mode with an unrelated unknown, and return the report.
fn rg10_report(
    policy: &str,
    input: &str,
    condition_mode: evaluation_trace::ConditionMode,
    partial_eval: bool,
) -> serde_json::Value {
    let entry = "data.t.deny";
    let mut engine = Engine::new();
    engine.add_policy("t.rego".into(), policy.into()).unwrap();
    let compiled = engine.compile_with_entrypoint(&Rc::from(entry)).unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entry]).unwrap();
    let mut vm = rvm::RegoVM::new_with_policy(compiled);
    vm.load_program(program);
    vm.set_explanation_settings(evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode: evaluation_trace::ValueMode::Full,
        condition_mode,
        detail: evaluation_trace::ExplanationDetail::Full,
        assume_unknown_input: partial_eval,
        eval_mode: if partial_eval {
            evaluation_trace::EvaluationMode::PartialEval
        } else {
            evaluation_trace::EvaluationMode::Causality
        },
        unknowns: if partial_eval {
            vec!["input.unrelated".into()]
        } else {
            Vec::new()
        },
        ..Default::default()
    });
    vm.set_input(Value::from_json_str(input).unwrap());
    let result = vm.execute_entry_point_by_name(entry).unwrap();
    serde_json::from_str(&vm.take_causality_report(result).unwrap()).unwrap()
}

/// Every reported condition of `data.t.deny`, including nested
/// `helper_conditions`, with its nesting depth.
fn rg10_conditions(report: &serde_json::Value) -> Vec<(usize, serde_json::Value)> {
    fn walk(
        condition: &serde_json::Value,
        depth: usize,
        out: &mut Vec<(usize, serde_json::Value)>,
    ) {
        out.push((depth, condition.clone()));
        for inner in condition["helper_conditions"]
            .as_array()
            .into_iter()
            .flatten()
        {
            walk(inner, depth + 1, out);
        }
    }
    let mut out = Vec::new();
    for rule in report["rules"].as_array().expect("rules") {
        if rule["name"] != "data.t.deny" {
            continue;
        }
        for group in ["definitions", "emissions"] {
            for item in rule[group].as_array().into_iter().flatten() {
                for condition in item["conditions"].as_array().into_iter().flatten() {
                    walk(condition, 0, &mut out);
                }
            }
        }
    }
    out
}

fn rg10_modes() -> [(evaluation_trace::ConditionMode, bool); 4] {
    use evaluation_trace::ConditionMode::{AllContributing, PrimaryOnly};
    [
        (PrimaryOnly, false),
        (AllContributing, false),
        (PrimaryOnly, true),
        (AllContributing, true),
    ]
}

/// The conditions whose text is exactly `text`; panics when there are none.
fn rg10_find(report: &serde_json::Value, text: &str) -> Vec<(usize, serde_json::Value)> {
    let found: Vec<_> = rg10_conditions(report)
        .into_iter()
        .filter(|(_, condition)| condition["text"] == text)
        .collect();
    assert!(!found.is_empty(), "no condition `{text}` in {report:#}");
    found
}

const RG10_INPUT: &str = r#"{"r": {"httpsOnly": false, "tls": "1.0"}}"#;

#[test]
fn rg10_not_over_calls_and_locals_is_negated() {
    let cases = [
        (
            "package t\nimport rego.v1\n_secure if {\n    input.r.httpsOnly == true\n    input.r.tls == \"1.2\"\n}\ndeny contains \"x\" if {\n    not _secure\n}\n",
            "not _secure",
        ),
        (
            "package t\nimport rego.v1\n_secure(r) if {\n    r.httpsOnly == true\n    r.tls == \"1.2\"\n}\ndeny contains \"x\" if {\n    not _secure(input.r)\n}\n",
            "not _secure(input.r)",
        ),
        (
            "package t\nimport rego.v1\n_secure(r) if r.httpsOnly == true\n_secure(r) if r.tls == \"1.2\"\ndeny contains \"x\" if {\n    not _secure(input.r)\n}\n",
            "not _secure(input.r)",
        ),
        (
            "package t\nimport rego.v1\n_https(r) if r.httpsOnly == true\n_bad(r) if {\n    r.tls != \"1.2\"\n    not _https(r)\n}\ndeny contains \"x\" if {\n    _bad(input.r)\n}\n",
            "not _https(r)",
        ),
        (
            "package t\nimport rego.v1\ndeny contains \"x\" if {\n    ok := input.r.tls == \"1.2\"\n    not ok\n}\n",
            "not ok",
        ),
        // A reference into a value with no input path (an array literal).
        (
            "package t\nimport rego.v1\ndeny contains \"x\" if {\n    some r in [input.r]\n    not r.missing\n}\n",
            "not r.missing",
        ),
    ];
    for (policy, text) in cases {
        for (mode, partial_eval) in rg10_modes() {
            let report = rg10_report(policy, RG10_INPUT, mode, partial_eval);
            for (_, condition) in rg10_find(&report, text) {
                assert_eq!(
                    condition["negated"], true,
                    "{mode:?} pe={partial_eval}: `{text}` must be negated: {condition:#}"
                );
                assert_eq!(condition["kind"], "truthiness", "{condition:#}");
                assert_eq!(condition["outcome"], "success", "{condition:#}");
            }
        }
    }
}

#[test]
fn rg10_helper_rule_names_the_called_rule_in_both_polarities() {
    let cases = [
        // (policy, input, condition text, expected helper_rule, expected depth)
        (
            "package t\nimport rego.v1\n_secure if {\n    input.r.httpsOnly == true\n    input.r.tls == \"1.2\"\n}\ndeny contains \"x\" if {\n    not _secure\n}\n",
            RG10_INPUT,
            "not _secure",
            "data.t._secure",
            0,
        ),
        (
            "package t\nimport rego.v1\n_secure(r) if r.httpsOnly == true\n_secure(r) if r.tls == \"1.2\"\ndeny contains \"x\" if {\n    not _secure(input.r)\n}\n",
            RG10_INPUT,
            "not _secure(input.r)",
            "data.t._secure",
            0,
        ),
        // Positive call that holds.
        (
            "package t\nimport rego.v1\n_weak(r) if r.tls != \"1.2\"\ndeny contains \"x\" if {\n    _weak(input.r)\n}\n",
            RG10_INPUT,
            "_weak(input.r)",
            "data.t._weak",
            0,
        ),
        // Positive call that fails.
        (
            "package t\nimport rego.v1\n_weak(r) if r.tls != \"1.2\"\ndeny contains \"x\" if {\n    _weak(input.r)\n}\n",
            r#"{"r": {"httpsOnly": false, "tls": "1.2"}}"#,
            "_weak(input.r)",
            "data.t._weak",
            0,
        ),
        // Nested inside a helper, and the outer call itself.
        (
            "package t\nimport rego.v1\n_https(r) if r.httpsOnly == true\n_bad(r) if {\n    r.tls != \"1.2\"\n    not _https(r)\n}\ndeny contains \"x\" if {\n    _bad(input.r)\n}\n",
            RG10_INPUT,
            "not _https(r)",
            "data.t._https",
            1,
        ),
        (
            "package t\nimport rego.v1\n_https(r) if r.httpsOnly == true\n_bad(r) if {\n    r.tls != \"1.2\"\n    not _https(r)\n}\ndeny contains \"x\" if {\n    _bad(input.r)\n}\n",
            RG10_INPUT,
            "_bad(input.r)",
            "data.t._bad",
            0,
        ),
    ];
    for (policy, input, text, rule, depth) in cases {
        for (mode, partial_eval) in rg10_modes() {
            let report = rg10_report(policy, input, mode, partial_eval);
            for (found_depth, condition) in rg10_find(&report, text) {
                assert_eq!(found_depth, depth, "{condition:#}");
                assert_eq!(
                    condition["helper_rule"], rule,
                    "{mode:?} pe={partial_eval}: `{text}` must name its helper: {condition:#}"
                );
                // A call read through `not` is negated; a direct call is not.
                assert_eq!(
                    condition.get("negated").is_some(),
                    text.starts_with("not "),
                    "{condition:#}"
                );
            }
        }
    }
}

#[test]
fn rg10_depth_cut_call_still_names_its_rule() {
    let mut policy = String::from("package t\nimport rego.v1\n\n");
    policy.push_str("h10(r) if {\n    r.tls == \"1.2\"\n    r.httpsOnly == true\n}\n");
    for level in (1..10).rev() {
        policy.push_str(&format!(
            "h{level}(r) if {{\n    r.tls != \"x\"\n    h{}(r)\n}}\n",
            level + 1
        ));
    }
    policy.push_str("deny contains \"x\" if {\n    not h1(input.r)\n}\n");
    for (mode, partial_eval) in rg10_modes() {
        let report = rg10_report(&policy, RG10_INPUT, mode, partial_eval);
        let cut: Vec<_> = rg10_conditions(&report)
            .into_iter()
            .filter(|(_, condition)| condition["helper_conditions_truncated"] == true)
            .collect();
        assert!(
            !cut.is_empty(),
            "{mode:?}: the chain must be cut: {report:#}"
        );
        for (_, condition) in cut {
            let rule = condition["helper_rule"]
                .as_str()
                .unwrap_or_else(|| panic!("a cut call must still name its rule: {condition:#}"));
            assert!(rule.starts_with("data.t.h"), "{condition:#}");
        }
    }
}

#[test]
fn rg10_controls_keep_their_shape() {
    let policy = "package t\nimport rego.v1\n_weak(r) if r.tls != \"1.2\"\ndeny contains \"x\" if {\n    r := input.r\n    r.tls != \"1.2\"\n    not r.httpsOnly == true\n    not startswith(r.tls, \"2\")\n    not r.missing\n    _weak(r)\n}\n";
    for (mode, partial_eval) in rg10_modes() {
        let report = rg10_report(policy, RG10_INPUT, mode, partial_eval);
        for (_, condition) in rg10_find(&report, "_weak(r)") {
            assert!(condition.get("negated").is_none(), "{condition:#}");
            assert_eq!(condition["helper_rule"], "data.t._weak", "{condition:#}");
        }
        for (_, condition) in rg10_find(&report, "r.tls != \"1.2\"") {
            assert!(condition.get("helper_rule").is_none(), "{condition:#}");
            assert!(condition.get("negated").is_none(), "{condition:#}");
        }
        for (_, condition) in rg10_find(&report, "not r.httpsOnly == true") {
            assert_eq!(condition["kind"], "comparison", "{condition:#}");
            assert_eq!(condition["negated"], true, "{condition:#}");
            assert!(condition.get("helper_rule").is_none(), "{condition:#}");
        }
        for (_, condition) in rg10_find(&report, "not startswith(r.tls, \"2\")") {
            assert_eq!(condition["kind"], "builtin", "{condition:#}");
            assert_eq!(condition["negated"], true, "{condition:#}");
        }
        for (_, condition) in rg10_find(&report, "not r.missing") {
            assert_eq!(condition["negated"], true, "{condition:#}");
            assert_eq!(
                condition["left"]["provenance"], "input.r.missing",
                "{condition:#}"
            );
            assert_eq!(condition["left"]["absent"], true, "{condition:#}");
        }
    }
}
