// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::*;
use crate::explain::UnknownPath;
use crate::languages::rego::compiler::Compiler;
use crate::rvm::program::{FunctionInfo, RuleInfo, RuleType};
use crate::rvm::vm::VmError;
use crate::rvm::{Instruction, Program};
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
fn provisional_conditions_survive_body_error_accounting() -> anyhow::Result<()> {
    let policy = r#"package test
allow if {
  input.u == 1
  some x in [1, "bad"]
  1 / x > 0
}"#;
    let result = pe(policy, "{}", &["u"])?;
    assert_eq!(result.status, ResidualStatus::Unsupported);
    assert_eq!(result.result, Value::Undefined);
    assert!(result.residual_queries.is_empty());
    assert_eq!(pe(policy, r#"{"u": 1}"#, &[])?.result, Value::Bool(true));
    assert_eq!(pe(policy, r#"{"u": 2}"#, &[])?.result, Value::Undefined);
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
        ("allow if h\nh if true", ResidualStatus::Exact),
    ];
    for (rules, want) in cases {
        let rego = format!("package test\n{rules}");
        let r = pe(&rego, r#"{"k": 1}"#, &["u"])?;
        assert_eq!(r.status, want, "{rules}");
        let unsupported = want == ResidualStatus::Unsupported;
        assert_eq!(r.warnings.len(), usize::from(unsupported), "{rules}");
        if unsupported {
            assert_eq!(r.result, Value::Undefined, "{rules}");
        }
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
fn nested_undefined_residual_values_fail_closed() -> anyhow::Result<()> {
    use alloc::collections::BTreeMap;
    for known in [
        Value::from(vec![Value::Undefined]),
        Value::from(BTreeMap::from([(Value::from("x"), Value::Undefined)])),
    ] {
        for rule in [
            "allow if input.u == input.known",
            "allow := input.known if input.u == 1",
        ] {
            let mut machine = vm(&format!("package test\n{rule}"))?;
            machine.set_input(Value::from(BTreeMap::from([(
                Value::from("known"),
                known.clone(),
            )])));
            let mut settings = PartialEvalSettings::default();
            settings.unknowns = keys(&["u"]);
            machine.set_partial_eval_settings(settings);
            let result = machine.partial_eval("data.test.allow")?;
            assert_eq!(result.status, ResidualStatus::Unsupported, "{rule}");
            assert!(result.residual_queries.is_empty());
        }
    }
    // Neither null nor the literal string "<undefined>" is an undefined value.
    let result = pe(
        "package test\nallow if input.u == input.known",
        r#"{"known": [null, "<undefined>"]}"#,
        &["u"],
    )?;
    assert_eq!(result.status, ResidualStatus::Exact);
    assert_eq!(
        texts(&result),
        vec![vec![r#"input.u == [null,"<undefined>"]"#]]
    );
    Ok(())
}

#[test]
fn lossy_numeric_residuals_fail_closed() -> anyhow::Result<()> {
    for rule in [
        "allow if input.u == 18446744073709551617",
        "allow := 18446744073709551617 if input.u == 1",
        "allow if input.u == [18446744073709551617]",
        "allow if input.u == 1000000000000000128.0",
    ] {
        let result = pe(&format!("package test\n{rule}"), "{}", &["u"])?;
        assert_eq!(
            result.status,
            ResidualStatus::Unsupported,
            "{rule}: {:?}",
            texts(&result)
        );
        assert!(result.residual_queries.is_empty());
    }
    for number in [
        "18446744073709551615",
        "-9223372036854775808",
        "0.1",
        "9007199254740994.0",
        "100000000000000000000000.0",
    ] {
        let result = pe(
            &format!("package test\nallow if input.u == {number}"),
            "{}",
            &["u"],
        )?;
        assert_eq!(result.status, ResidualStatus::Exact, "{number}");
        assert_eq!(
            result.residual_queries[0].conditions[0].value,
            Some(Value::from_json_str(number)?)
        );
        let value = result.residual_queries[0].conditions[0]
            .value
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("numeric condition has no value"))?;
        assert_eq!(Value::from_json_str(&value.to_json_str_compact()?)?, *value);
    }
    let policy = "package test\nallow if input.u == 100000000000000000000000.0";
    assert_eq!(pe(policy, r#"{"u":1e23}"#, &[])?.result, Value::Bool(true));
    Ok(())
}

#[test]
fn defined_false_results_are_not_undefined() -> anyhow::Result<()> {
    let concrete = pe("package test\nallow := false", "{}", &[])?;
    assert_eq!(concrete.status, ResidualStatus::Exact);
    assert_eq!(concrete.result, Value::Bool(false));
    assert!(concrete.residual_queries.is_empty());
    let policy = "package test\nallow := false if input.u == 1";
    let residual = pe(policy, "{}", &["u"])?;
    assert_eq!(residual.status, ResidualStatus::Exact);
    assert_eq!(residual.result, Value::Undefined);
    assert_eq!(texts(&residual), vec![vec!["input.u == 1"]]);
    assert_eq!(residual.residual_queries[0].value, Value::Bool(false));
    assert_eq!(pe(policy, r#"{"u":1}"#, &[])?.result, Value::Bool(false));
    assert_eq!(pe(policy, r#"{"u":2}"#, &[])?.result, Value::Undefined);
    Ok(())
}

#[test]
fn deeply_nested_known_values_remain_exact() -> anyhow::Result<()> {
    use alloc::collections::BTreeMap;
    let mut known = Value::Null;
    for _ in 0..16_384 {
        known = Value::from(vec![known]);
    }
    let mut machine = vm("package test\nallow if input.u == input.known")?;
    machine.set_input(Value::from(BTreeMap::from([(
        Value::from("known"),
        known.clone(),
    )])));
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = keys(&["u"]);
    machine.set_partial_eval_settings(settings);
    let result = machine.partial_eval("data.test.allow")?;
    assert_eq!(result.status, ResidualStatus::Exact);
    assert_eq!(
        result.residual_queries[0].conditions[0].value.as_ref(),
        Some(&known)
    );
    Ok(())
}

#[cfg(feature = "std")]
#[test]
fn residual_value_scan_checks_the_execution_timer() -> anyhow::Result<()> {
    use crate::utils::limits::{acquire_limits_test_lock, ExecutionTimerConfig};
    use core::{num::NonZeroU32, time::Duration};

    let _guard = acquire_limits_test_lock();
    let mut machine = vm(TWO_CONDITIONS)?;
    let mut known = Value::Null;
    for _ in 0..20 {
        known = Value::from(vec![known.clone(), known]);
    }
    let mut state = machine.validate_unknowns()?;
    state.shadow.insert(
        0,
        Taint::Unknown {
            path: (UnknownRoot::Input, vec![PathSegment::Key("u".into())]),
            used: false,
        },
    );
    machine.pe = Some(Box::new(state));
    machine.registers = vec![Value::Undefined, known, Value::Undefined];
    machine.set_execution_timer_config(Some(ExecutionTimerConfig {
        limit: Duration::ZERO,
        check_interval: NonZeroU32::MIN,
    }));
    assert!(matches!(
        machine.pe_compare(Some(2), 0, 1, Operator::Eq),
        Err(VmError::TimeLimitExceeded { .. })
    ));
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
fn known_azure_entry_returns_do_not_consume_cached_input() -> anyhow::Result<()> {
    use crate::languages::azure_policy::{compiler, parser};

    let source = crate::lexer::Source::from_contents(
        "policy.json".into(),
        r#"{"if":{"field":"type","equals":"wanted"},"then":{"effect":"deny"}}"#.into(),
    )?;
    let rule = parser::parse_policy_rule(&source).map_err(|error| anyhow::anyhow!("{error}"))?;
    let program = compiler::compile_policy_rule(&rule)?;
    let mut machine = RegoVM::new();
    machine.load_program(Arc::new((*program).clone()));
    for resource_type in ["other", "wanted"] {
        machine.set_input(Value::from_json_str(&format!(
            r#"{{"resource":{{"type":"{resource_type}"}}}}"#
        ))?);
        let expected = machine.execute_entry_point_by_name("main")?;
        for unknowns in [vec![], keys(&["resource.u"])] {
            let mut settings = PartialEvalSettings::default();
            settings.unknowns = unknowns;
            machine.set_partial_eval_settings(settings);
            let result = machine.partial_eval("main")?;
            assert_eq!(result.status, ResidualStatus::Exact, "{resource_type}");
            assert_eq!(result.result, expected);
        }
    }
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
        vm.load_program(alloc::sync::Arc::new((*program).clone()));
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

#[test]
fn a_recorder_cannot_be_installed() -> anyhow::Result<()> {
    struct Recorder;
    impl crate::explain::ExplanationRecorder for Recorder {}
    let mut vm = vm(TWO_CONDITIONS)?;
    vm.set_explanation_recorder(Box::new(Recorder));
    assert_eq!(
        vm.partial_eval("data.test.allow"),
        Err(ExplainError::PartialEvalWithRecorder)
    );
    assert!(vm.take_explanation_recorder().is_some());
    assert_eq!(
        vm.partial_eval("data.test.allow")?.status,
        ResidualStatus::Exact
    );
    Ok(())
}

#[test]
fn other_errors_after_a_read_are_unsupported() -> anyhow::Result<()> {
    // Compiled rule bodies absorb non-fatal errors, so the error is raised
    // outside a rule.
    let mut program = Program::new();
    program.add_instruction(Instruction::LoadInput { dest: 0 }, None);
    program.add_instruction(
        Instruction::Eq {
            dest: 0,
            left: 0,
            right: 0,
        },
        None,
    );
    program.add_instruction(Instruction::LoadTrue { dest: 0 }, None);
    program.add_instruction(Instruction::LoadNull { dest: 1 }, None);
    program.add_instruction(
        Instruction::Lt {
            dest: 0,
            left: 0,
            right: 1,
        },
        None,
    );
    program.add_instruction(Instruction::Return { value: 0 }, None);
    program.add_entry_point("entry".into(), 0);
    let program = alloc::sync::Arc::new(program);
    let run = |unknowns: Vec<UnknownPath>| {
        let mut vm = RegoVM::new();
        vm.set_strict_builtin_errors(true);
        vm.load_program(program.clone());
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = unknowns;
        vm.set_partial_eval_settings(settings);
        vm.partial_eval("entry")
    };
    let result = run(keys(&["u"]))?;
    assert_eq!(result.status, ResidualStatus::Unsupported);
    assert_eq!(result.warnings.len(), 1);
    let context_u = UnknownPath::new(UnknownRoot::Context, [PathSegment::Key("u".into())]);
    for unknowns in [vec![], vec![context_u]] {
        let result = run(unknowns.clone());
        assert!(
            matches!(
                result,
                Err(ExplainError::Vm(VmError::ArithmeticError { .. }))
            ),
            "{unknowns:?}: {result:?}"
        );
    }
    Ok(())
}

#[test]
fn entry_points_returning_an_unknown_rule_kind_are_rejected() -> anyhow::Result<()> {
    let run = |entry_pc: usize, rule_type: RuleType, function: bool| {
        let mut program = Program::new();
        program.add_instruction(Instruction::LoadInput { dest: 0 }, None);
        program.add_instruction(Instruction::Return { value: 0 }, None);
        program.add_entry_point("entry".into(), entry_pc);
        let mut rule = RuleInfo::new(
            "data.test.r".into(),
            rule_type,
            crate::Rc::new(vec![]),
            0,
            1,
        );
        if function {
            rule.function_info = Some(FunctionInfo {
                param_names: vec![],
                num_params: 0,
            });
        }
        program.rule_infos.push(rule);
        let mut vm = RegoVM::new();
        vm.load_program(alloc::sync::Arc::new(program));
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = keys(&["u"]);
        vm.set_partial_eval_settings(settings);
        vm.partial_eval("entry")
    };
    assert_eq!(run(0, RuleType::Complete, false)?.kind, RuleKind::Complete);
    let unknown_kind = Err(ExplainError::PartialEvalUnknownRuleKind {
        entry: "entry".to_string(),
    });
    assert_eq!(run(0, RuleType::PartialSet, false), unknown_kind);
    assert_eq!(run(0, RuleType::Complete, true), unknown_kind);
    // A malformed entry point fails as the VM reports it.
    let result = run(9, RuleType::PartialSet, false);
    assert!(
        matches!(
            result,
            Err(ExplainError::Vm(VmError::EntryPointPcOutOfBounds { .. }))
        ),
        "{result:?}"
    );
    let mut program = Program::new();
    program.add_instruction(
        Instruction::CallRule {
            dest: 0,
            rule_index: 5,
        },
        None,
    );
    program.add_instruction(Instruction::Return { value: 0 }, None);
    program.add_entry_point("entry".into(), 0);
    program.rule_infos.push(RuleInfo::new(
        "data.test.r".into(),
        RuleType::PartialSet,
        crate::Rc::new(vec![]),
        0,
        1,
    ));
    let mut vm = RegoVM::new();
    vm.load_program(alloc::sync::Arc::new(program));
    let result = vm.partial_eval("entry");
    assert!(
        matches!(
            result,
            Err(ExplainError::Vm(VmError::RuleIndexOutOfBounds { .. }))
        ),
        "{result:?}"
    );
    Ok(())
}

#[test]
fn fatal_errors_are_not_unsupported() -> anyhow::Result<()> {
    let run = |rego: &str, unknown: &UnknownPath, max_instructions: Option<usize>| {
        let mut vm = vm(rego)?;
        vm.set_input(Value::from_json_str(
            r#"{"k": 1, "a": 1e308, "p": "([a-z]{1,64}){1,64}"}"#,
        )?);
        if let Some(max) = max_instructions {
            vm.set_max_instructions(max);
        }
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = vec![unknown.clone()];
        vm.set_partial_eval_settings(settings);
        anyhow::Ok(vm.partial_eval("data.test.allow"))
    };
    let looping = "package test\nallow if {\n  _u := input.u\n  input.k == 1\n  some i in numbers.range(1, 100000)\n  i < 0\n}";
    #[cfg(feature = "regex")]
    let regex = "package test\nallow if { _u := input.u; regex.match(input.p, \"test\") }";
    let overflow = "package test\nallow if {\n  _u := input.u\n  input.k == 1\n  y := input.a + input.a\n  y > 0\n}";
    // Nothing is flagged with an unknown under `context`, so those cases
    // only check that the error isn't lost; the unchecked unknown read under
    // `input` must not turn a later fatal error into Unsupported.
    let context_u = UnknownPath::new(UnknownRoot::Context, [PathSegment::Key("u".into())]);
    for unknown in [context_u, UnknownPath::input_keys(["u"])] {
        let result = run(looping, &unknown, Some(1000))?;
        assert!(
            matches!(
                result,
                Err(ExplainError::Vm(VmError::InstructionLimitExceeded { .. }))
            ),
            "{unknown:?}: {result:?}"
        );
        #[cfg(feature = "regex")]
        {
            let result = run(regex, &unknown, None)?;
            assert!(
                matches!(
                    result,
                    Err(ExplainError::Vm(VmError::RegexSizeLimitExceeded { .. }))
                ),
                "{unknown:?}: {result:?}"
            );
        }
        let result = run(overflow, &unknown, None)?;
        assert!(
            matches!(
                result,
                Err(ExplainError::Vm(VmError::NumericOverflow { .. }))
            ),
            "{unknown:?}: {result:?}"
        );
    }
    Ok(())
}

#[test]
fn host_await_identifiers_consume_unknowns() -> anyhow::Result<()> {
    for reference in ["input", "input.u"] {
        let source =
            format!("package test\nallow := __builtin_host_await(\"payload\", {reference})");
        for respond in [false, true] {
            let mut machine = vm(&source)?;
            machine.set_input(Value::new_object());
            if respond {
                let identifier = if reference == "input" {
                    Value::new_object()
                } else {
                    Value::Undefined
                };
                machine.set_host_await_responses([(identifier, [Value::Bool(true)])]);
            }
            let mut settings = PartialEvalSettings::default();
            settings.unknowns = keys(&["u"]);
            machine.set_partial_eval_settings(settings);
            assert_eq!(
                machine.partial_eval("data.test.allow")?.status,
                ResidualStatus::Unsupported,
                "{reference}, respond={respond}"
            );
        }
    }
    for respond in [false, true] {
        let mut machine = vm("package test\nallow := __builtin_host_await(\"payload\", input.u)")?;
        machine.set_input(Value::from_json_str(r#"{"u":"ok"}"#)?);
        if respond {
            machine.set_host_await_responses([(Value::from("ok"), [Value::Bool(true)])]);
        }
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = keys(&["other"]);
        machine.set_partial_eval_settings(settings);
        let result = machine.partial_eval("data.test.allow")?;
        assert_eq!(result.status, ResidualStatus::Exact);
        assert_eq!(
            result.result,
            if respond {
                Value::Bool(true)
            } else {
                Value::Undefined
            }
        );
    }
    Ok(())
}

#[test]
fn implicit_entry_results_consume_unknowns() -> anyhow::Result<()> {
    for ending in [
        None,
        Some(Instruction::DestructuringSuccess {}),
        Some(Instruction::Return { value: 0 }),
    ] {
        let mut program = Program::new();
        program.add_instruction(Instruction::LoadInput { dest: 0 }, None);
        if let Some(ending) = ending {
            program.add_instruction(ending, None);
        }
        program.add_entry_point("entry".into(), 0);
        let mut machine = RegoVM::new();
        machine.load_program(Arc::new(program));
        machine.set_input(Value::new_object());
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = keys(&["u"]);
        machine.set_partial_eval_settings(settings);
        assert_eq!(
            machine.partial_eval("entry")?.status,
            ResidualStatus::Unsupported
        );
        machine.set_partial_eval_settings(PartialEvalSettings::default());
        let result = machine.partial_eval("entry")?;
        assert_eq!(result.status, ResidualStatus::Exact);
        assert_eq!(result.result, Value::new_object());
    }
    Ok(())
}

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
fn chained_index_skips_keys_after_known_undefined() -> anyhow::Result<()> {
    use crate::rvm::instructions::{ChainedIndexParams, LiteralOrRegister};

    let mut program = Program::new();
    program.literals.push(Value::from("missing"));
    let params_index = program
        .instruction_data
        .add_chained_index_params(ChainedIndexParams {
            dest: 1,
            root: 0,
            path_components: alloc::vec![
                LiteralOrRegister::Literal(0),
                LiteralOrRegister::Register(255),
            ],
        });
    program.add_instruction(Instruction::LoadInput { dest: 0 }, None);
    program.add_instruction(Instruction::ChainedIndex { params_index }, None);
    program.add_instruction(Instruction::Return { value: 1 }, None);
    program.add_entry_point("entry".into(), 0);
    let mut machine = RegoVM::new();
    machine.load_program(Arc::new(program));
    machine.set_base_register_count(2);
    for input in ["{}", r#"{"missing":{}}"#] {
        machine.set_input(Value::from_json_str(input)?);
        for unknowns in [vec![], keys(&["u"])] {
            let mut settings = PartialEvalSettings::default();
            settings.unknowns = unknowns;
            machine.set_partial_eval_settings(settings);
            let result = machine.partial_eval("entry");
            if input == "{}" {
                let result = result?;
                assert_eq!(result.status, ResidualStatus::Exact);
                assert_eq!(result.result, Value::Undefined);
            } else {
                assert!(
                    matches!(
                        result,
                        Err(ExplainError::Vm(VmError::RegisterIndexOutOfBounds {
                            index: 255,
                            ..
                        }))
                    ),
                    "{result:?}"
                );
            }
        }
    }
    Ok(())
}

#[test]
fn shadow_indexing_preserves_invalid_register_errors() -> anyhow::Result<()> {
    let mut program = Program::new();
    program.add_instruction(Instruction::LoadInput { dest: 0 }, None);
    program.add_instruction(
        Instruction::Index {
            dest: 1,
            container: 0,
            key: 255,
        },
        None,
    );
    program.add_instruction(Instruction::Return { value: 1 }, None);
    program.add_entry_point("entry".into(), 0);
    let program = Arc::new(program);
    for unknowns in [vec![], keys(&["u"])] {
        let mut machine = RegoVM::new();
        machine.load_program(program.clone());
        machine.set_base_register_count(2);
        machine.set_input(Value::new_object());
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = unknowns;
        machine.set_partial_eval_settings(settings);
        let result = machine.partial_eval("entry");
        assert!(
            matches!(
                result,
                Err(ExplainError::Vm(VmError::RegisterIndexOutOfBounds {
                    index: 255,
                    ..
                }))
            ),
            "{result:?}"
        );
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
fn unknowns_index_values_as_rego_does() -> anyhow::Result<()> {
    use alloc::collections::{BTreeMap, BTreeSet};
    let run = |input: Value, segments: [PathSegment; 2]| {
        let mut vm = vm(TWO_CONDITIONS)?;
        vm.set_input(input);
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = vec![UnknownPath::new(UnknownRoot::Input, segments)];
        vm.set_partial_eval_settings(settings);
        anyhow::Ok(vm.partial_eval("data.test.allow").map(|_| ()))
    };
    let field =
        |name: &str, value: Value| Value::from(BTreeMap::from([(Value::from(name), value)]));
    let xs0 = || [PathSegment::Key("xs".into()), PathSegment::Index(0)];
    let supplied = |path: &str| Err(ExplainError::UnknownValueSupplied { path: path.into() });

    // Rego reads `input.xs[0]` from a number key and `input.s.a` from a set.
    let numbered = Value::from(BTreeMap::from([(Value::from(0), Value::from(1))]));
    assert_eq!(run(field("xs", numbered), xs0())?, supplied("input.xs[0]"));
    let set = Value::from(BTreeSet::from([Value::from("a")]));
    let s_a = [PathSegment::Key("s".into()), PathSegment::Key("a".into())];
    assert_eq!(run(field("s", set), s_a)?, supplied("input.s.a"));
    Ok(())
}

#[test]
fn context_and_index_unknowns_are_validated() -> anyhow::Result<()> {
    let run = |unknowns: Vec<UnknownPath>, input: &str, context: Option<&str>| {
        let mut vm = vm(TWO_CONDITIONS)?;
        vm.set_input(Value::from_json_str(input)?);
        if let Some(context) = context {
            vm.set_context(Value::from_json_str(context)?);
        }
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = unknowns;
        vm.set_partial_eval_settings(settings);
        anyhow::Ok(
            vm.partial_eval("data.test.allow")
                .map_err(|e| e.to_string()),
        )
    };
    let context_u = || UnknownPath::new(UnknownRoot::Context, [PathSegment::Key("u".into())]);
    let xs0 = || {
        UnknownPath::new(
            UnknownRoot::Input,
            [PathSegment::Key("xs".into()), PathSegment::Index(0)],
        )
    };
    let whole = |root| UnknownPath::new(root, []);
    let supplied = |path: &str| Err(format!("a value is supplied for unknown path `{path}`"));

    assert_eq!(
        run(vec![context_u()], "{}", Some(r#"{"u": 1}"#))?.map(|_| ()),
        supplied("context.u")
    );
    run(vec![context_u()], "{}", Some(r#"{"v": 1}"#))?.map_err(anyhow::Error::msg)?;
    // Unlike input, context is undefined until it is set, so null is a value.
    assert_eq!(
        run(vec![whole(UnknownRoot::Context)], "{}", Some("null"))?.map(|_| ()),
        supplied("context")
    );
    run(vec![whole(UnknownRoot::Context)], "{}", None)?.map_err(anyhow::Error::msg)?;

    assert_eq!(
        run(vec![xs0()], r#"{"xs": [5]}"#, None)?.map(|_| ()),
        supplied("input.xs[0]")
    );
    run(vec![xs0()], r#"{"xs": []}"#, None)?.map_err(anyhow::Error::msg)?;
    // A string key is not the number index.
    run(vec![xs0()], r#"{"xs": {"0": 1}}"#, None)?.map_err(anyhow::Error::msg)?;

    // Paths under different roots don't overlap; a whole root overlaps its paths.
    let input_u = UnknownPath::input_keys(["u"]);
    run(vec![input_u.clone(), context_u()], "{}", None)?.map_err(anyhow::Error::msg)?;
    assert_eq!(
        run(vec![whole(UnknownRoot::Input), input_u], "null", None)?.map(|_| ()),
        Err("invalid unknown path `input.u`: overlaps `input`".into())
    );
    // Keys are quoted as JSON strings.
    let odd = UnknownPath::input_keys(["a\"b", ""]);
    assert_eq!(
        run(vec![odd.clone(), odd], "{}", None)?.map(|_| ()),
        Err(r#"invalid unknown path `input["a\"b"][""]`: overlaps `input["a\"b"][""]`"#.into())
    );
    Ok(())
}

#[test]
fn invalid_unknown_messages_render_paths() -> anyhow::Result<()> {
    let message = |unknowns: &[&str], input: &str| {
        pe(TWO_CONDITIONS, input, unknowns)
            .err()
            .map(|e| e.to_string())
    };
    assert_eq!(
        message(&["user", "user.role"], "{}").as_deref(),
        Some("invalid unknown path `input.user.role`: overlaps `input.user`")
    );
    assert_eq!(
        message(&["a.b"], r#"{"a": {"b": 1}}"#).as_deref(),
        Some("a value is supplied for unknown path `input.a.b`")
    );
    assert_eq!(message(&["a.b"], r#"{"a.b": 1}"#), None);
    // A key that is not an identifier is quoted.
    let mut vm = vm(TWO_CONDITIONS)?;
    vm.set_input(Value::from_json_str(r#"{"a.b": {"in": 1}}"#)?);
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = vec![UnknownPath::input_keys(["a.b", "in"])];
    vm.set_partial_eval_settings(settings);
    assert_eq!(
        vm.partial_eval("data.test.allow")
            .err()
            .map(|e| e.to_string()),
        Some(String::from(
            r#"a value is supplied for unknown path `input["a.b"]["in"]`"#
        ))
    );
    Ok(())
}
