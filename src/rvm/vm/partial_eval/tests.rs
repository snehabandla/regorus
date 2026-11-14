// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::*;
use crate::explain::UnknownPath;
use crate::languages::rego::compiler::Compiler;
use crate::Engine;
use alloc::string::ToString as _;
use alloc::sync::Arc;
use alloc::vec;

fn vm(rego: &str) -> anyhow::Result<RegoVM> {
    let mut engine = Engine::new();
    engine.add_policy("p.rego".into(), rego.into())?;
    let compiled = engine.compile_with_entrypoint(&"data.test.allow".into())?;
    let mut vm = RegoVM::new();
    vm.load_program(Compiler::compile_from_policy(
        &compiled,
        &["data.test.allow"],
    )?);
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

const TWO_CONDITIONS: &str = r#"package test
allow if {
  input.user.role == "admin"
  input.action == "delete"
}"#;

#[test]
fn reading_an_unknown_root_is_unsupported() -> anyhow::Result<()> {
    let run = |body: &str, root: UnknownRoot| -> anyhow::Result<PartialEvalResult> {
        let mut vm = vm(&format!("package test\nallow if {{ {body} }}"))?;
        vm.set_input(Value::from_json_str(r#"{"k": 1, "s": "xy"}"#)?);
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = vec![UnknownPath::new(root, [PathSegment::Key("u".into())])];
        vm.set_partial_eval_settings(settings);
        Ok(vm.partial_eval("data.test.allow")?)
    };
    let cases = [
        ("input.u", Value::Undefined),
        ("input.u + 1 > 2", Value::Undefined),
        ("input.k == 1", Value::from(true)),
        ("input.k == 2", Value::Undefined),
        (r#"startswith(input.s, "x")"#, Value::from(true)),
        ("count(input) == 2", Value::from(true)),
        ("not input.u", Value::from(true)),
        ("some x in [1, 2]; input.k == x", Value::from(true)),
    ];
    for (body, concrete) in cases {
        let result = run(body, UnknownRoot::Input)?;
        assert_eq!(result.status, ResidualStatus::Unsupported, "{body}");
        assert_eq!(result.result, Value::Undefined, "{body}");
        assert!(result.residual_queries.is_empty(), "{body}");
        let want =
            "partial evaluation unsupported: `input` has unknown paths and is read at p.rego:2:";
        assert!(
            result.warnings.len() == 1 && result.warnings[0].starts_with(want),
            "{body}: {:?}",
            result.warnings
        );
        // With the unknown under the other root, the concrete result is exact.
        let result = run(body, UnknownRoot::Context)?;
        assert_eq!(result.status, ResidualStatus::Exact, "{body}");
        assert_eq!(result.kind, RuleKind::Complete);
        assert_eq!(result.result, concrete, "{body}");
        assert!(result.residual_queries.is_empty(), "{body}");
        assert!(result.warnings.is_empty(), "{body}: {:?}", result.warnings);
    }
    Ok(())
}

#[test]
fn repeated_evaluations_are_isolated() -> anyhow::Result<()> {
    let mut vm = vm(TWO_CONDITIONS)?;
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = keys(&["user", "action"]);
    vm.set_partial_eval_settings(settings.clone());
    let first = vm.partial_eval("data.test.allow")?;
    assert_eq!(first.status, ResidualStatus::Unsupported);
    // An unsupported evaluation leaves nothing behind.
    vm.set_input(Value::from_json_str(
        r#"{"user": {"role": "admin"}, "action": "delete"}"#,
    )?);
    vm.set_partial_eval_settings(PartialEvalSettings::default());
    let concrete = vm.partial_eval("data.test.allow")?;
    assert_eq!(concrete.status, ResidualStatus::Exact);
    assert_eq!(concrete.result, Value::from(true));
    assert!(concrete.warnings.is_empty());
    assert_eq!(
        vm.execute_entry_point_by_name("data.test.allow")?,
        Value::from(true)
    );
    vm.set_input(Value::new_object());
    vm.set_partial_eval_settings(settings);
    assert_eq!(vm.partial_eval("data.test.allow")?, first);
    Ok(())
}

#[test]
fn whole_input_unknown() -> anyhow::Result<()> {
    let mut vm = vm("package test\nallow if input.role == \"admin\"")?;
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = vec![UnknownPath::new(UnknownRoot::Input, [])];
    vm.set_partial_eval_settings(settings);
    // Comparisons with unknown input are not supported yet.
    let result = vm.partial_eval("data.test.allow")?;
    assert_eq!(result.status, ResidualStatus::Unsupported);
    vm.set_input(Value::new_object());
    assert!(matches!(
        vm.partial_eval("data.test.allow"),
        Err(ExplainError::UnknownValueSupplied { .. })
    ));
    Ok(())
}

#[test]
fn invalid_unknown_messages_render_paths() {
    let message = |unknowns: &[&str], input: &str| {
        pe(TWO_CONDITIONS, input, unknowns)
            .err()
            .map(|e| e.to_string())
    };
    assert_eq!(
        message(&["user", "user.role"], "{}").as_deref(),
        Some(r#"invalid unknown path `input["user"]["role"]`: overlaps `input["user"]`"#)
    );
    assert_eq!(
        message(&["a.b"], r#"{"a": {"b": 1}}"#).as_deref(),
        Some(r#"a value is supplied for unknown path `input["a"]["b"]`"#)
    );
    assert_eq!(message(&["a.b"], r#"{"a.b": 1}"#), None);
}

#[test]
fn calls_fail_closed() -> anyhow::Result<()> {
    let cases = [
        (
            "allow if f(input.u)\nf(x) if x == 1",
            ResidualStatus::Unsupported,
        ),
        // Any read of an input root with unknowns, until the shadow lands.
        (
            "allow if f(input.k)\nf(x) if x == 1",
            ResidualStatus::Unsupported,
        ),
        ("allow if h\nh if input.u == 1", ResidualStatus::Unsupported),
        // Helpers can't read an input root with unknowns.
        ("allow if h\nh if input.k == 1", ResidualStatus::Unsupported),
        ("allow if h\nh if data.x == null", ResidualStatus::Exact),
    ];
    for (rules, want) in cases {
        let rego = format!("package test\n{rules}");
        let r = pe(&rego, r#"{"k": 1}"#, &["u"])?;
        assert_eq!(r.status, want, "{rules}");
        // Warnings point at the policy, not at the entry stub.
        assert!(
            r.warnings
                .iter()
                .all(|w| w.contains(" at p.rego:") && !w.ends_with(":0:0")),
            "{rules}: {:?}",
            r.warnings
        );
    }
    Ok(())
}

#[test]
fn with_is_rejected_by_the_compiler() {
    let rego = "package test\nallow if { input.u == 1 with input as {} }";
    let err = vm(rego).err().map(|e| format!("{e:?}").to_lowercase());
    assert!(err.as_ref().is_some_and(|e| e.contains("with")), "{err:?}");
}

#[test]
fn invalid_unknowns_are_errors() -> anyhow::Result<()> {
    let cases: [(&[&str], &str, &str); 4] = [
        (&["user", "user.role"], "{}", "overlap"),
        (&["user.role", "user"], "{}", "overlap"),
        (&["a", "a"], "{}", "overlap"),
        (&["user.role"], r#"{"user": {"role": "x"}}"#, "supplied"),
    ];
    for (unknowns, input, want) in cases {
        let err = pe(TWO_CONDITIONS, input, unknowns);
        let err = err.err().and_then(|e| e.downcast::<ExplainError>().ok());
        let got = match err {
            Some(ExplainError::InvalidUnknownPath { .. }) => "overlap",
            Some(ExplainError::UnknownValueSupplied { .. }) => "supplied",
            _ => "other",
        };
        assert_eq!(got, want, "{unknowns:?}");
    }
    // Siblings and a supplied sibling value are fine.
    let input = r#"{"user": {"name": "x"}}"#;
    pe(TWO_CONDITIONS, input, &["user.role", "user.id", "action"])?;
    Ok(())
}

#[test]
fn suspendable_mode_is_an_error() -> anyhow::Result<()> {
    let mut vm = vm(TWO_CONDITIONS)?;
    vm.set_execution_mode(ExecutionMode::Suspendable);
    assert_eq!(
        vm.partial_eval("data.test.allow"),
        Err(ExplainError::PartialEvalSuspendable)
    );
    vm.set_execution_mode(ExecutionMode::RunToCompletion);
    vm.partial_eval("data.test.allow")?;
    Ok(())
}

#[cfg(feature = "azure_policy")]
#[test]
fn context_unknowns_fail_closed() -> anyhow::Result<()> {
    use crate::languages::azure_policy::{compiler, parser};
    let run = |condition: &str| -> anyhow::Result<PartialEvalResult> {
        let json = format!(r#"{{"if": {condition}, "then": {{"effect": "deny"}}}}"#);
        let source = crate::lexer::Source::from_contents("policy.json".into(), json)?;
        let rule = parser::parse_policy_rule(&source).map_err(|e| anyhow::anyhow!("{e}"))?;
        let program = compiler::compile_policy_rule(&rule)?;
        let mut vm = RegoVM::new();
        vm.load_program(Arc::new((*program).clone()));
        vm.set_input(Value::from_json_str(
            r#"{"resource": {}, "parameters": {}}"#,
        )?);
        vm.set_context(Value::from_json_str(
            r#"{"resourceGroup": {"location": "eastus"}}"#,
        )?);
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = vec![UnknownPath::new(
            UnknownRoot::Context,
            [
                PathSegment::Key("resourceGroup".into()),
                PathSegment::Key("name".into()),
            ],
        )];
        vm.set_partial_eval_settings(settings);
        Ok(vm.partial_eval("main")?)
    };
    let name = r#"{"value": "[resourceGroup().name]", "equals": "rg"}"#;
    let result = run(name)?;
    assert_eq!(result.status, ResidualStatus::Unsupported);
    assert!(
        result.warnings.len() == 1 && result.warnings[0].contains("`context` has unknown paths"),
        "{:?}",
        result.warnings
    );
    // Any read of a context root with unknowns, until the shadow lands.
    let location = r#"{"value": "[resourceGroup().location]", "equals": "eastus"}"#;
    let result = run(location)?;
    assert_eq!(result.status, ResidualStatus::Unsupported);
    let field = r#"{"field": "type", "equals": "x"}"#;
    let result = run(field)?;
    assert_eq!(result.status, ResidualStatus::Exact);
    Ok(())
}
