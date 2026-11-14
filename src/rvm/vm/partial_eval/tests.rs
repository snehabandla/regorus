// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::*;
use crate::explain::UnknownPath;
use crate::languages::rego::compiler::Compiler;
use crate::Engine;
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
fn reading_an_unknown_is_unsupported() -> anyhow::Result<()> {
    let result = pe("package test\nallow if input.u + 1 > 2", "{}", &["u"])?;
    assert_eq!(result.status, ResidualStatus::Unsupported);
    assert_eq!(result.result, Value::Undefined);
    assert!(result.residual_queries.is_empty());
    assert_eq!(
        result.warnings,
        vec![String::from(
            "partial evaluation unsupported: `Add` reads a value that depends on unknown input at p.rego:2:18"
        )]
    );
    // Without a read of the unknown path the concrete result is exact.
    let rego = "package test\nallow if input.k + 1 > 1";
    for (input, want) in [
        (r#"{"k": 1}"#, Value::from(true)),
        (r#"{"k": -1}"#, Value::Undefined),
    ] {
        let result = pe(rego, input, &["u"])?;
        assert_eq!(result.status, ResidualStatus::Exact, "{input}");
        assert_eq!(result.kind, RuleKind::Complete);
        assert_eq!(result.result, want, "{input}");
        assert!(result.residual_queries.is_empty());
        assert!(result.warnings.is_empty(), "{:?}", result.warnings);
    }
    Ok(())
}

#[test]
fn checks_on_unknowns_are_unsupported() -> anyhow::Result<()> {
    for (body, instruction) in [
        ("input.u", "Guard"),
        ("input.u == 1", "Eq"),
        ("1 < input.u", "Lt"),
    ] {
        let rego = format!("package test\nallow if {body}");
        let result = pe(&rego, "{}", &["u"])?;
        assert_eq!(result.status, ResidualStatus::Unsupported, "{body}");
        let want = format!("`{instruction}` reads a value that depends on unknown input");
        assert!(
            result.warnings.len() == 1 && result.warnings[0].contains(&want),
            "{body}: {:?}",
            result.warnings
        );
        // The same check on known input is exact.
        let rego = rego.replace("input.u", "input.k");
        let result = pe(&rego, r#"{"k": 2}"#, &["u"])?;
        assert_eq!(result.status, ResidualStatus::Exact, "{body}");
        assert!(result.warnings.is_empty(), "{body}");
    }
    Ok(())
}

#[test]
fn unchecked_unknowns_are_unsupported() -> anyhow::Result<()> {
    let input = r#"{"k": 1, "user": {"name": "a"}}"#;
    let unknowns = &["u", "user.role"];
    let cases = [
        (
            "allow if { _v := input.u }",
            "a value that depends on unknown input is not checked",
        ),
        // The supplied part of `input.user` is incomplete.
        (
            "allow := input.user",
            "the rule value depends on unknown input",
        ),
    ];
    for (rules, want) in cases {
        let result = pe(&format!("package test\n{rules}"), input, unknowns)?;
        assert_eq!(result.status, ResidualStatus::Unsupported, "{rules}");
        let want = format!("partial evaluation unsupported: {want} at p.rego:2:");
        assert!(
            result.warnings.len() == 1 && result.warnings[0].starts_with(&want),
            "{rules}: {:?}",
            result.warnings
        );
    }
    let twins = [
        ("allow if { _v := input.k }", Value::from(true)),
        ("allow := input.user.name", Value::from("a")),
    ];
    for (rules, want) in twins {
        let result = pe(&format!("package test\n{rules}"), input, unknowns)?;
        assert_eq!(result.status, ResidualStatus::Exact, "{rules}");
        assert_eq!(result.result, want, "{rules}");
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
fn parent_of_unknown_is_unsupported() -> anyhow::Result<()> {
    let unknowns = &["user.role"];
    for body in ["count(input.user) > 0", "input.user", "input == {}"] {
        let rego = format!("package test\nallow if {body}");
        let result = pe(&rego, r#"{"user": {"name": "a"}}"#, unknowns)?;
        assert_eq!(result.status, ResidualStatus::Unsupported, "{body}");
        assert_eq!(result.warnings.len(), 1);
    }
    // A sibling of the unknown path is known.
    let rego = "package test\nallow if count(input.user.name) > 0";
    let result = pe(rego, r#"{"user": {"name": "a"}}"#, unknowns)?;
    assert_eq!(result.status, ResidualStatus::Exact);
    assert_eq!(result.result, Value::from(true));
    Ok(())
}

#[test]
fn unchecked_reads_fail_closed() -> anyhow::Result<()> {
    let cases = [
        // Arithmetic.
        ("input.u + 1 > 2", ResidualStatus::Unsupported),
        ("input.k + 1 > 2", ResidualStatus::Exact),
        // Builtins.
        (
            r#"object.get(input, "u", 1) == 1"#,
            ResidualStatus::Unsupported,
        ),
        (r#"startswith(input.u, "x")"#, ResidualStatus::Unsupported),
        (r#"startswith(input.s, "x")"#, ResidualStatus::Exact),
        // Assignment without a check.
        ("_v := input.u", ResidualStatus::Unsupported),
        ("_v := input.k", ResidualStatus::Exact),
        ("x := input.u == 1", ResidualStatus::Unsupported),
        // Loops.
        ("some x in input.u; x == 1", ResidualStatus::Unsupported),
        (
            "some x in [1, 2]; input.u == x",
            ResidualStatus::Unsupported,
        ),
        ("some x in [1, 2]; input.k == x", ResidualStatus::Exact),
        (
            "every x in [1] { input.u == x }",
            ResidualStatus::Unsupported,
        ),
        // `not`.
        ("not input.u == 1", ResidualStatus::Unsupported),
        ("not input.u", ResidualStatus::Unsupported),
        ("not input.k == 2", ResidualStatus::Exact),
        // Comprehensions.
        (
            "count([x | x := input.u]) == 1",
            ResidualStatus::Unsupported,
        ),
        (
            "count([x | x := input.u; x == 1]) == 0",
            ResidualStatus::Unsupported,
        ),
        ("count([x | x := input.k]) == 1", ResidualStatus::Exact),
        // Collections.
        ("[input.u] == [1]", ResidualStatus::Unsupported),
        ("[input.k] == [1]", ResidualStatus::Exact),
        // Unknown against unknown, or as an index.
        ("input.u == input.w", ResidualStatus::Unsupported),
        ("[1, 2][input.u] == 2", ResidualStatus::Unsupported),
        ("[1, 2][input.k] == 2", ResidualStatus::Exact),
    ];
    for (body, want) in cases {
        let rego = format!("package test\nallow if {{ {body} }}");
        let result = pe(&rego, r#"{"k": 1, "s": "xy"}"#, &["u", "w"])?;
        assert_eq!(result.status, want, "{body}");
        assert_eq!(
            result.warnings.is_empty(),
            want == ResidualStatus::Exact,
            "{body}"
        );
    }
    // A checked assignment reads the unknown in a comparison, which is not
    // supported yet.
    let result = pe(
        "package test\nallow if { _v := input.u; _v == 1 }",
        "{}",
        &["u"],
    )?;
    assert_eq!(result.status, ResidualStatus::Unsupported);
    Ok(())
}

#[test]
fn calls_fail_closed() -> anyhow::Result<()> {
    let cases = [
        (
            "allow if f(input.u)\nf(x) if x == 1",
            ResidualStatus::Unsupported,
        ),
        ("allow if f(input.k)\nf(x) if x == 1", ResidualStatus::Exact),
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
    let location = r#"{"value": "[resourceGroup().location]", "equals": "eastus"}"#;
    let result = run(location)?;
    assert_eq!(result.status, ResidualStatus::Exact);
    Ok(())
}
