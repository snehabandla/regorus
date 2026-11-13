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
        vec![vec![
            r#"input.user.role == "admin""#,
            r#"input.action == "delete""#
        ]]
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

#[test]
fn operators_are_mirrored_onto_the_input_path() -> anyhow::Result<()> {
    let cases = [
        ("18 < input.age", "input.age > 18"),
        ("18 <= input.age", "input.age >= 18"),
        ("18 > input.age", "input.age < 18"),
        ("18 >= input.age", "input.age <= 18"),
        ("18 == input.age", "input.age == 18"),
        ("18 != input.age", "input.age != 18"),
        ("input.age < 18", "input.age < 18"),
        ("input.age >= 18", "input.age >= 18"),
    ];
    for (body, want) in cases {
        let result = pe(&format!("package test\nallow if {body}"), "{}", &["age"])?;
        assert_eq!(texts(&result), vec![vec![want]], "{body}");
    }
    let result = pe("package test\nallow if 18 < input.age", "{}", &["age"])?;
    let condition = &result.residual_queries[0].conditions[0];
    assert_eq!(condition.operator, Some(Operator::Gt));
    assert_eq!(condition.value, Some(Value::from(18_u64)));
    Ok(())
}

#[test]
fn keys_are_segments_not_dotted_text() -> anyhow::Result<()> {
    let rego = "package test\nallow if input[\"a.b\"] == 1";
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = vec![UnknownPath::input_keys(["a.b"])];
    let mut vm = vm(rego)?;
    vm.set_partial_eval_settings(settings);
    let result = vm.partial_eval("data.test.allow")?;
    assert_eq!(texts(&result), vec![vec![r#"input["a.b"] == 1"#]]);
    let condition = &result.residual_queries[0].conditions[0];
    assert_eq!(condition.input_path.as_deref(), Some(r#"input["a.b"]"#));
    // `input.a.b` is a different path.
    let result = pe(rego, r#"{"a.b": 1}"#, &["a.b"])?;
    assert_eq!(result.status, ResidualStatus::Exact);
    assert_eq!(result.result, Value::from(true));
    Ok(())
}

#[test]
fn array_indices_and_keywords_render_as_rego() -> anyhow::Result<()> {
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = vec![UnknownPath::new(
        UnknownRoot::Input,
        [
            PathSegment::Key("xs".into()),
            PathSegment::Index(1),
            PathSegment::Key("not".into()),
        ],
    )];
    let mut vm = vm("package test\nallow if input.xs[1][\"not\"] == true")?;
    vm.set_input(Value::from_json_str(r#"{"xs": [{}, {}]}"#)?);
    vm.set_partial_eval_settings(settings);
    let result = vm.partial_eval("data.test.allow")?;
    assert_eq!(texts(&result), vec![vec![r#"input.xs[1]["not"] == true"#]]);
    Ok(())
}

#[test]
fn truthiness_guard() -> anyhow::Result<()> {
    let result = pe("package test\nallow if input.enabled", "{}", &["enabled"])?;
    assert_eq!(texts(&result), vec![vec!["input.enabled"]]);
    let condition = &result.residual_queries[0].conditions[0];
    assert_eq!(condition.kind, ResidualKind::Truthy);
    assert_eq!(condition.operator, None);
    let result = pe(
        "package test\nallow if input.enabled",
        r#"{"enabled": false}"#,
        &[],
    )?;
    assert_eq!(result.status, ResidualStatus::Exact);
    assert_eq!(result.result, Value::Undefined);
    Ok(())
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
fn budget_overflow_is_unsupported() -> anyhow::Result<()> {
    for (max, want) in [
        (3, ResidualStatus::Exact),
        (2, ResidualStatus::Exact),
        (1, ResidualStatus::Unsupported),
    ] {
        let mut vm = vm(TWO_CONDITIONS)?;
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = keys(&["user", "action"]);
        settings.max_conditions = max;
        vm.set_partial_eval_settings(settings);
        let result = vm.partial_eval("data.test.allow")?;
        assert_eq!(result.status, want, "{max}");
        if want == ResidualStatus::Unsupported {
            assert_eq!(
                result.warnings,
                vec![String::from("residual budget exceeded")]
            );
        }
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
    assert_eq!(texts(&first).len(), 1);
    // An unsupported evaluation leaves nothing behind.
    let mut over_budget = settings.clone();
    over_budget.max_conditions = 0;
    vm.set_partial_eval_settings(over_budget);
    assert_eq!(
        vm.partial_eval("data.test.allow")?.status,
        ResidualStatus::Unsupported
    );
    vm.set_input(Value::from_json_str(
        r#"{"user": {"role": "admin"}, "action": "delete"}"#,
    )?);
    vm.set_partial_eval_settings(PartialEvalSettings::default());
    let concrete = vm.partial_eval("data.test.allow")?;
    assert_eq!(concrete.result, Value::from(true));
    assert!(concrete.residual_queries.is_empty());
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
    // A checked assignment is a residual on the input path.
    let result = pe(
        "package test\nallow if { _v := input.u; _v == 1 }",
        "{}",
        &["u"],
    )?;
    assert_eq!(texts(&result), vec![vec!["input.u == 1"]]);
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
    assert!(vm(rego).is_err());
}

#[test]
fn only_a_single_complete_body_gets_conditions() -> anyhow::Result<()> {
    let cases = [
        (
            "allow if input.u == 1\nallow if input.k == 1",
            ResidualStatus::Unsupported,
        ),
        (
            "allow if input.u == 1 else := false",
            ResidualStatus::Unsupported,
        ),
        (
            "default allow := false\nallow if input.u == 1",
            ResidualStatus::Unsupported,
        ),
        (
            "allow := input.u if input.k == 1",
            ResidualStatus::Unsupported,
        ),
        ("allow := {1} if input.u == 1", ResidualStatus::Unsupported),
        ("allow if input.u == {1}", ResidualStatus::Unsupported),
        ("allow := [1] if input.u == [1]", ResidualStatus::Exact),
        // No dependency on unknown input: the concrete result is exact.
        (
            "allow if input.k == 1\nallow if input.k == 1",
            ResidualStatus::Exact,
        ),
        (
            "default allow := false\nallow if input.k == 2",
            ResidualStatus::Exact,
        ),
        ("allow := {1} if input.k == 1", ResidualStatus::Exact),
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
    let result = pe("package test\nallow := [1] if input.u == [1]", "{}", &["u"])?;
    assert_eq!(
        result.residual_queries[0].value,
        Value::from_json_str("[1]")?
    );
    assert_eq!(texts(&result), vec![vec!["input.u == [1]"]]);
    Ok(())
}

#[test]
fn strict_ordering_may_raise_so_is_unsupported() -> anyhow::Result<()> {
    for (body, want) in [
        ("input.u < 1", ResidualStatus::Unsupported),
        ("input.u == 1", ResidualStatus::Exact),
    ] {
        let mut vm = vm(&format!("package test\nallow if {body}"))?;
        vm.set_strict_builtin_errors(true);
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = keys(&["u"]);
        vm.set_partial_eval_settings(settings);
        assert_eq!(vm.partial_eval("data.test.allow")?.status, want, "{body}");
    }
    Ok(())
}

#[test]
fn deployment_unknowns() -> anyhow::Result<()> {
    let rego = r#"package test
allow if {
  input.resource.type == "vm"
  input.deployment.location != "eastus"
  input.deployment.targetScope == "resourceGroup"
}"#;
    let unknowns = &["deployment.location", "deployment.targetScope"];
    let input = r#"{"resource": {"type": "vm"}, "deployment": {"tenantId": "t"}}"#;
    let result = pe(rego, input, unknowns)?;
    assert_eq!(
        texts(&result),
        vec![vec![
            r#"input.deployment.location != "eastus""#,
            r#"input.deployment.targetScope == "resourceGroup""#
        ]]
    );
    let input = r#"{"resource": {"type": "storage"}}"#;
    let result = pe(rego, input, unknowns)?;
    assert_eq!(result.status, ResidualStatus::Exact);
    assert!(result.residual_queries.is_empty());
    Ok(())
}

#[test]
fn whole_input_unknown() -> anyhow::Result<()> {
    let mut vm = vm("package test\nallow if input.role == \"admin\"")?;
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = vec![UnknownPath::new(UnknownRoot::Input, [])];
    vm.set_partial_eval_settings(settings);
    let result = vm.partial_eval("data.test.allow")?;
    assert_eq!(texts(&result), vec![vec![r#"input.role == "admin""#]]);
    vm.set_input(Value::new_object());
    assert!(matches!(
        vm.partial_eval("data.test.allow"),
        Err(ExplainError::UnknownValueSupplied { .. })
    ));
    Ok(())
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
    assert!(pe(TWO_CONDITIONS, input, &["user.role", "user.id", "action"]).is_ok());
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
    assert!(vm.partial_eval("data.test.allow").is_ok());
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
