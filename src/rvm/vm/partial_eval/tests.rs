// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::*;
use crate::explain::UnknownPath;
use crate::languages::rego::compiler::Compiler;
use crate::Engine;
use alloc::vec;

fn vm(rego: &str) -> anyhow::Result<RegoVM> {
    let mut engine = Engine::new();
    engine.add_policy("p.rego".into(), rego.into())?;
    let compiled = engine.compile_with_entrypoint(&"data.test.allow".into())?;
    let mut vm = RegoVM::new();
    vm.load_program(Compiler::compile_from_policy(&compiled, &["data.test.allow"])?);
    Ok(vm)
}

fn keys(paths: &[&str]) -> Vec<UnknownPath> {
    paths
        .iter()
        .map(|p| UnknownPath::input_keys(p.split('.')))
        .collect()
}

/// Partially evaluates `data.test.allow` with `input` and unknown
/// dotted `input` paths.
fn pe(rego: &str, input: &str, unknowns: &[&str]) -> anyhow::Result<PartialEvalResult> {
    let mut vm = vm(rego)?;
    vm.set_input(Value::from_json_str(input)?);
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = keys(unknowns);
    vm.set_partial_eval_settings(settings);
    Ok(vm.partial_eval("data.test.allow")?)
}

fn texts(result: &PartialEvalResult) -> Vec<Vec<&str>> {
    result
        .residual_queries
        .iter()
        .map(|q| q.conditions.iter().map(|c| c.text.as_str()).collect())
        .collect()
}

const TWO_CONDITIONS: &str = r#"package test
allow if {
  input.user.role == "admin"
  input.action == "delete"
}"#;

#[test]
fn two_conditions_residual() -> anyhow::Result<()> {
    let result = pe(TWO_CONDITIONS, "{}", &["user", "action"])?;
    assert_eq!(result.status, ResidualStatus::Exact);
    assert_eq!(result.result, Value::Undefined);
    assert_eq!(
        texts(&result),
        vec![vec![r#"input.user.role == "admin""#, r#"input.action == "delete""#]]
    );
    let query = &result.residual_queries[0];
    assert_eq!(query.value, Value::from(true));
    let role = &query.conditions[0];
    assert_eq!(role.kind, ResidualKind::ConditionHolds);
    assert_eq!(role.operator, Some(Operator::Eq));
    assert_eq!(role.input_path.as_deref(), Some("input.user.role"));
    assert_eq!(role.value, Some(Value::from("admin")));
    assert_eq!(role.rule.as_deref(), Some("data.test.allow"));
    let location = role.location.as_ref().map(|l| (l.file.as_str(), l.line));
    assert_eq!(location, Some(("p.rego", 3)));
    Ok(())
}

#[test]
fn known_checks_eliminate_or_drop_out() -> anyhow::Result<()> {
    let result = pe(TWO_CONDITIONS, r#"{"action": "read"}"#, &["user"])?;
    assert_eq!(result.status, ResidualStatus::Exact);
    assert_eq!(result.result, Value::Undefined);
    assert!(result.residual_queries.is_empty());
    let result = pe(TWO_CONDITIONS, r#"{"action": "delete"}"#, &["user"])?;
    assert_eq!(texts(&result), vec![vec![r#"input.user.role == "admin""#]]);
    let input = r#"{"user": {"role": "admin"}, "action": "delete"}"#;
    let result = pe(TWO_CONDITIONS, input, &[])?;
    assert_eq!(result.status, ResidualStatus::Exact);
    assert_eq!(result.result, Value::from(true));
    assert!(result.residual_queries.is_empty());
    Ok(())
}
