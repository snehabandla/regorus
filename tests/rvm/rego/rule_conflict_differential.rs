// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Differential test for conflicting complete-rule and function definitions.
//!
//! When two definitions of a complete rule (or two definitions of a function
//! for the same arguments) both succeed with different values, OPA and the
//! interpreter abort the query with a conflict error. The RVM must do the same
//! in both execution modes, also when the conflicting rule is only reached
//! through another rule, a `not`, a comprehension, `every` or a partial set, and it
//! must not fall back to the rule's default. Non-conflicting definitions, `else`
//! chains and defaults keep their usual results. The expected outcomes were
//! checked against OPA 1.2.0.

use anyhow::{anyhow, bail, Result};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::{Engine, Value};

const COMPLETE_MESSAGE: &[&str] = &[
    "conflicts",
    "complete rules must not produce multiple outputs",
];
const FUNCTION_MESSAGE: &[&str] = &[
    "multiple outputs",
    "functions must not produce multiple outputs for same inputs",
];

enum Expect {
    Value(&'static str),
    Conflict {
        rule: &'static str,
        message: &'static [&'static str],
    },
}

struct Case {
    name: &'static str,
    policy: &'static str,
    entrypoint: &'static str,
    input: &'static str,
    expect: Expect,
}

const UNDEFINED: &str = "#undefined";

const BOTH: &str = r#"{"a": true, "b": true, "n": 10}"#;
const ONLY_A: &str = r#"{"a": true, "n": 3}"#;
const NEITHER: &str = r#"{"n": -1}"#;

const COMPLETE: &str = r#"package test
x := 1 if input.a
x := 2 if input.b
"#;

const FUNCTION: &str = r#"package test
f(v) := 1 if v > 0
f(v) := 2 if v > 5
r := f(input.n)
"#;

const HELPER: &str = r#"package test
helper := "a" if input.a
helper := "b" if input.b
uses if helper == "a"
negated if not helper == "z"
negated_fn if not f(input.n) == 3
in_comprehension := [y | some i in [1, 2]; y := concat("", [helper, format_int(i, 10)])]
in_every if {
  every i in [1, 2] {
    helper != sprintf("%d", [i])
  }
}
in_set contains helper if true
f(v) := 1 if v > 0
f(v) := 2 if v > 5
"#;

const SAME: &str = r#"package test
x := 1 if input.a
x := 1 if input.b
f(v) := 1 if v > 0
f(v) := 1 if v > 5
r := f(input.n)
"#;

const ELSE: &str = r#"package test
x := 1 if input.a
else := 2 if input.b
f(v) := 1 if v > 0
else := 2 if v > 5
r := f(input.n)
"#;

const DEFAULT: &str = r#"package test
default x := 0
x := 1 if input.a
x := 2 if input.b
default f(_) := 0
f(v) := 1 if v > 0
f(v) := 2 if v > 5
r := f(input.n)
"#;

fn cases() -> Vec<Case> {
    let conflict = |rule| Expect::Conflict {
        rule,
        message: COMPLETE_MESSAGE,
    };
    let fn_conflict = |rule| Expect::Conflict {
        rule,
        message: FUNCTION_MESSAGE,
    };
    let case = |name, policy, entrypoint, input, expect| Case {
        name,
        policy,
        entrypoint,
        input,
        expect,
    };
    vec![
        case(
            "complete conflict",
            COMPLETE,
            "data.test.x",
            BOTH,
            conflict("data.test.x"),
        ),
        case(
            "complete one definition",
            COMPLETE,
            "data.test.x",
            ONLY_A,
            Expect::Value("1"),
        ),
        case(
            "complete no definition",
            COMPLETE,
            "data.test.x",
            NEITHER,
            Expect::Value(UNDEFINED),
        ),
        case(
            "function conflict",
            FUNCTION,
            "data.test.r",
            BOTH,
            fn_conflict("data.test.f"),
        ),
        case(
            "function one definition",
            FUNCTION,
            "data.test.r",
            ONLY_A,
            Expect::Value("1"),
        ),
        case(
            "helper rule conflict",
            HELPER,
            "data.test.uses",
            BOTH,
            conflict("data.test.helper"),
        ),
        case(
            "helper rule conflict under not",
            HELPER,
            "data.test.negated",
            BOTH,
            conflict("data.test.helper"),
        ),
        case(
            "function conflict under not",
            HELPER,
            "data.test.negated_fn",
            BOTH,
            fn_conflict("data.test.f"),
        ),
        case(
            "helper rule conflict in comprehension",
            HELPER,
            "data.test.in_comprehension",
            BOTH,
            conflict("data.test.helper"),
        ),
        case(
            "helper rule conflict in every",
            HELPER,
            "data.test.in_every",
            BOTH,
            conflict("data.test.helper"),
        ),
        case(
            "helper rule conflict in partial set",
            HELPER,
            "data.test.in_set",
            BOTH,
            conflict("data.test.helper"),
        ),
        case(
            "helper rule one definition",
            HELPER,
            "data.test.negated",
            ONLY_A,
            Expect::Value("true"),
        ),
        case(
            "same value twins",
            SAME,
            "data.test.x",
            BOTH,
            Expect::Value("1"),
        ),
        case(
            "same value function twins",
            SAME,
            "data.test.r",
            BOTH,
            Expect::Value("1"),
        ),
        case(
            "else twins",
            ELSE,
            "data.test.x",
            BOTH,
            Expect::Value("1"),
        ),
        case(
            "else function twins",
            ELSE,
            "data.test.r",
            BOTH,
            Expect::Value("1"),
        ),
        case(
            "default twins",
            DEFAULT,
            "data.test.x",
            BOTH,
            conflict("data.test.x"),
        ),
        case(
            "default function twins",
            DEFAULT,
            "data.test.r",
            BOTH,
            fn_conflict("data.test.f"),
        ),
        case(
            "default without definition",
            DEFAULT,
            "data.test.x",
            NEITHER,
            Expect::Value("0"),
        ),
    ]
}

fn want_value(want: &str) -> Result<Value> {
    if want == UNDEFINED {
        return Ok(Value::Undefined);
    }
    Value::from_json_str(want)
}

fn run_rvm(case: &Case, input: &Value, mode: ExecutionMode) -> Result<Result<Value, VmError>> {
    let mut engine = Engine::new();
    engine.add_policy("test.rego".to_string(), case.policy.to_string())?;
    let compiled = engine.compile_with_entrypoint(&case.entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[case.entrypoint])?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_execution_mode(mode);
    vm.set_input(input.clone());
    let result = vm.execute_entry_point_by_name(case.entrypoint);
    if mode == ExecutionMode::Suspendable && result.is_ok() {
        match vm.execution_state() {
            ExecutionState::Completed { .. } => {}
            ExecutionState::Error { error } => return Ok(Err(error.clone())),
            other => bail!("suspendable execution did not complete: {other:?}"),
        }
    }
    Ok(result)
}

fn check(case: &Case) -> Result<()> {
    let input = Value::from_json_str(case.input)?;

    let mut engine = Engine::new();
    engine.add_policy("test.rego".to_string(), case.policy.to_string())?;
    engine.set_input(input.clone());
    let interpreter = engine.eval_rule(case.entrypoint.to_string());
    match (&case.expect, &interpreter) {
        (Expect::Value(want), Ok(got)) if want_value(want)? == *got => {}
        (Expect::Conflict { .. }, Err(_)) => {}
        (_, got) => bail!("interpreter: unexpected result {got:?}"),
    }

    let mut failures = Vec::new();
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        if let Err(err) = check_rvm(case, &input, mode) {
            failures.push(format!("{err:#}"));
        }
    }
    if !failures.is_empty() {
        bail!("{}", failures.join("; "));
    }
    Ok(())
}

fn check_rvm(case: &Case, input: &Value, mode: ExecutionMode) -> Result<()> {
    let got = run_rvm(case, input, mode)?;
    match (&case.expect, got) {
        (Expect::Value(want), Ok(got)) if want_value(want)? == got => {}
        (Expect::Conflict { rule, message }, Err(err)) => {
            let wrapped = anyhow::Error::from(err);
            let vm_error = wrapped
                .downcast_ref::<VmError>()
                .ok_or_else(|| anyhow!("[{mode:?}] not a VmError: {wrapped:#}"))?;
            let VmError::RuleConflict {
                rule: got_rule,
                message: got_message,
                ..
            } = vm_error
            else {
                bail!("[{mode:?}] expected RuleConflict, got {vm_error:?}");
            };
            if got_rule != rule {
                bail!("[{mode:?}] conflict reported for {got_rule}, expected {rule}");
            }
            let display = vm_error.to_string();
            for part in *message {
                if !display.contains(part) {
                    bail!("[{mode:?}] error `{display}` lacks `{part}` ({got_message})");
                }
            }
        }
        (_, got) => bail!("[{mode:?}] RVM: unexpected result {got:?}"),
    }
    Ok(())
}

#[test]
fn rule_conflicts_match_interpreter() {
    let failures: Vec<String> = cases()
        .iter()
        .filter_map(|case| {
            check(case)
                .err()
                .map(|err| format!("{}: {err:#}", case.name))
        })
        .collect();
    assert!(
        failures.is_empty(),
        "{} rule conflict cases failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
