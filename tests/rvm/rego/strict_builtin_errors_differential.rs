// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Differential test for builtin and arithmetic errors with
//! `set_strict_builtin_errors`.
//!
//! In strict mode OPA (`--strict-builtin-errors`) and the interpreter abort the
//! query when a builtin or an arithmetic operator fails. The RVM must do the
//! same in both execution modes, also when the failure is reached through
//! `not`, `default`, `else`, a function, a comprehension, `every`, a partial
//! set or a package read. Without strict mode the failing expression is
//! Undefined. Every case runs in both modes; the expected outcomes were checked
//! against OPA 1.2.0 with operands read from input, so that OPA's type checker
//! cannot reject them at compile time.

use anyhow::{bail, Result};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::{Engine, Value};

enum Expect {
    Value(&'static str),
    /// Error whose message contains the given text for every engine.
    Error(&'static str),
    /// Error whose message differs between the interpreter and the RVM.
    Errors {
        interpreter: &'static str,
        rvm: &'static str,
    },
    /// Known RVM bug unrelated to strict errors: the interpreter (and OPA)
    /// return `want`, the RVM returns `rvm`.
    RvmDiverges {
        want: &'static str,
        rvm: &'static str,
    },
}

struct Case {
    name: &'static str,
    module: &'static str,
    entrypoint: &'static str,
    input: &'static str,
    strict: Expect,
    non_strict: Expect,
}

const UNDEFINED: &str = "#undefined";
const COUNT_ERROR: &str = "requires array/object/set/string";
const Y: &str = "data.test.y";

const COUNT: &str = "package test\ny := count(input.v)\n";
const DIV: &str = "package test\ny := input.a / input.b\n";
const MOD: &str = "package test\ny := input.a % input.b\n";
const ADD: &str = "package test\ny := input.a + input.b\n";
const SUB: &str = "package test\ny := input.a - input.b\n";
const MUL: &str = "package test\ny := input.a * input.b\n";
const TO_NUMBER: &str = "package test\ny := to_number(input.v)\n";
const LT: &str = "package test\ny := input.a < input.b\n";

const FUNCTION: &str = r#"package test
f(a, b) := a / b
y := f(input.a, input.b)
"#;

const NOT: &str = r#"package test
y if not count(input.v) == 7
"#;

const DEFAULT: &str = r#"package test
default y := 0
y := count(input.v)
"#;

const ELSE: &str = r#"package test
y := count(input.v) if { true } else := 7
"#;

const ELSE_AFTER_FAIL: &str = r#"package test
y := 1 if { false } else := count(input.v)
"#;

const PARTIAL_SET: &str = r#"package test
s contains count(x) if some x in input.vs
y := sort(s)
"#;

const COMPREHENSION: &str = r#"package test
y := [n | some x in input.vs; n := count(x)]
"#;

const EVERY: &str = r#"package test
y if every x in input.vs { count(x) > 0 }
"#;

const DEFAULT_FUNCTION: &str = r#"package test
default f(_) := 0
f(x) := count(x)
y := f(input.v)
"#;

const UNREFERENCED: &str = r#"package test
z := count(input.v)
y := 1
"#;

const PACKAGE_READ: &str = r#"package test
z := count(input.v)
y := 1
"#;

const PACKAGE_READER: &str = r#"package query
all := data.test
"#;

const V_BAD: &str = r#"{"v": 5}"#;
const V_OK: &str = r#"{"v": [1, 2]}"#;
const VS_BAD: &str = r#"{"vs": [[1], 5]}"#;
const VS_OK: &str = r#"{"vs": [[1], [1, 2]]}"#;

const fn case(
    name: &'static str,
    module: &'static str,
    input: &'static str,
    strict: Expect,
    non_strict: Expect,
) -> Case {
    Case {
        name,
        module,
        entrypoint: Y,
        input,
        strict,
        non_strict,
    }
}

fn cases() -> Vec<Case> {
    use Expect::{Error, Errors, RvmDiverges, Value as V};
    vec![
        case("count", COUNT, V_BAD, Error(COUNT_ERROR), V(UNDEFINED)),
        case("count twin", COUNT, V_OK, V("2"), V("2")),
        case("count undefined operand", COUNT, "{}", V(UNDEFINED), V(UNDEFINED)),
        case(
            "divide by zero",
            DIV,
            r#"{"a": 1, "b": 0}"#,
            Error("divide by zero"),
            V(UNDEFINED),
        ),
        case("divide twin", DIV, r#"{"a": 1, "b": 2}"#, V("0.5"), V("0.5")),
        case(
            "modulo by zero",
            MOD,
            r#"{"a": 1, "b": 0}"#,
            Error("modulo by zero"),
            V(UNDEFINED),
        ),
        case("modulo twin", MOD, r#"{"a": 5, "b": 3}"#, V("2"), V("2")),
        case(
            "modulo on float",
            MOD,
            r#"{"a": 1.5, "b": 1}"#,
            Error("modulo on floating-point number"),
            V(UNDEFINED),
        ),
        case(
            "add type error",
            ADD,
            r#"{"a": "x", "b": 1}"#,
            Errors {
                interpreter: "expects numeric argument",
                rvm: "Cannot add",
            },
            V(UNDEFINED),
        ),
        case("add twin", ADD, r#"{"a": 2, "b": 1}"#, V("3"), V("3")),
        case(
            "subtract type error",
            SUB,
            r#"{"a": [1], "b": 1}"#,
            Errors {
                interpreter: "expects numeric argument",
                rvm: "Cannot subtract",
            },
            V(UNDEFINED),
        ),
        case("subtract twin", SUB, r#"{"a": 3, "b": 1}"#, V("2"), V("2")),
        case(
            "multiply type error",
            MUL,
            r#"{"a": "x", "b": 2}"#,
            Errors {
                interpreter: "expects numeric argument",
                rvm: "Cannot multiply",
            },
            V(UNDEFINED),
        ),
        case(
            "divide type error",
            DIV,
            r#"{"a": "x", "b": 2}"#,
            Errors {
                interpreter: "expects numeric argument",
                rvm: "Cannot divide",
            },
            V(UNDEFINED),
        ),
        case(
            "to_number",
            TO_NUMBER,
            r#"{"v": "x"}"#,
            Error("could not parse string as number"),
            V(UNDEFINED),
        ),
        case("to_number twin", TO_NUMBER, r#"{"v": "4"}"#, V("4"), V("4")),
        case(
            "divide by zero in function",
            FUNCTION,
            r#"{"a": 1, "b": 0}"#,
            Error("divide by zero"),
            V(UNDEFINED),
        ),
        case(
            "function twin",
            FUNCTION,
            r#"{"a": 1, "b": 4}"#,
            V("0.25"),
            V("0.25"),
        ),
        case("not", NOT, V_BAD, Error(COUNT_ERROR), V("true")),
        case("not twin", NOT, V_OK, V("true"), V("true")),
        case("default", DEFAULT, V_BAD, Error(COUNT_ERROR), V("0")),
        case("default twin", DEFAULT, V_OK, V("2"), V("2")),
        case("else", ELSE, V_BAD, Error(COUNT_ERROR), V("7")),
        case("else twin", ELSE, V_OK, V("2"), V("2")),
        case(
            "else after failed body",
            ELSE_AFTER_FAIL,
            V_BAD,
            Error(COUNT_ERROR),
            V(UNDEFINED),
        ),
        case("else after failed body twin", ELSE_AFTER_FAIL, V_OK, V("2"), V("2")),
        case(
            "partial set",
            PARTIAL_SET,
            VS_BAD,
            Error(COUNT_ERROR),
            V("[1]"),
        ),
        case("partial set twin", PARTIAL_SET, VS_OK, V("[1, 2]"), V("[1, 2]")),
        case(
            "comprehension",
            COMPREHENSION,
            VS_BAD,
            Error(COUNT_ERROR),
            V("[1]"),
        ),
        case("comprehension twin", COMPREHENSION, VS_OK, V("[1, 2]"), V("[1, 2]")),
        case("every", EVERY, VS_BAD, Error(COUNT_ERROR), V(UNDEFINED)),
        case("every twin", EVERY, VS_OK, V("true"), V("true")),
        case(
            "default function",
            DEFAULT_FUNCTION,
            V_BAD,
            Error(COUNT_ERROR),
            V("0"),
        ),
        case("default function twin", DEFAULT_FUNCTION, V_OK, V("2"), V("2")),
        case("unreferenced failing rule", UNREFERENCED, V_BAD, V("1"), V("1")),
        // Comparing different types is not an error in OPA or the interpreter.
        // The RVM's strict mode turns it into Undefined; that is a separate
        // bug and must not become a hard error.
        case(
            "mixed-type comparison",
            LT,
            r#"{"a": 1, "b": "a"}"#,
            RvmDiverges {
                want: "true",
                rvm: UNDEFINED,
            },
            V("true"),
        ),
    ]
}

fn want_value(want: &str) -> Result<Value> {
    if want == UNDEFINED {
        return Ok(Value::Undefined);
    }
    Value::from_json_str(want)
}

fn new_engine(modules: &[&str], strict: bool) -> Result<Engine> {
    let mut engine = Engine::new();
    engine.set_strict_builtin_errors(strict);
    for (idx, module) in modules.iter().enumerate() {
        engine.add_policy(format!("test{idx}.rego"), (*module).to_string())?;
    }
    Ok(engine)
}

fn new_vm(modules: &[&str], entrypoint: &str, mode: ExecutionMode, strict: bool) -> Result<RegoVM> {
    let mut engine = new_engine(modules, strict)?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_execution_mode(mode);
    vm.set_strict_builtin_errors(strict);
    Ok(vm)
}

fn eval_vm(
    vm: &mut RegoVM,
    mode: ExecutionMode,
    entrypoint: &str,
    input: &Value,
) -> Result<Result<Value, VmError>> {
    vm.set_input(input.clone());
    let result = vm.execute_entry_point_by_name(entrypoint);
    if mode == ExecutionMode::Suspendable {
        match (&result, vm.execution_state()) {
            (Ok(_), ExecutionState::Completed { .. }) => {}
            (Err(err), ExecutionState::Error { error }) if err.to_string() == error.to_string() => {
            }
            (_, state) => bail!("suspendable execution returned {result:?} in state {state:?}"),
        }
    }
    Ok(result)
}

fn check_interpreter(expect: &Expect, got: &Result<Value>) -> Result<()> {
    match (expect, got) {
        (Expect::Value(want) | Expect::RvmDiverges { want, .. }, Ok(got))
            if want_value(want)? == *got => {}
        (
            Expect::Error(want)
            | Expect::Errors {
                interpreter: want, ..
            },
            Err(err),
        ) if format!("{err:#}").contains(want) => {}
        (_, got) => bail!("interpreter: unexpected result {got:?}"),
    }
    Ok(())
}

fn check_rvm(expect: &Expect, got: &Result<Value, VmError>, mode: ExecutionMode) -> Result<()> {
    match (expect, got) {
        (Expect::Value(want) | Expect::RvmDiverges { rvm: want, .. }, Ok(got))
            if want_value(want)? == *got => {}
        (Expect::Error(want) | Expect::Errors { rvm: want, .. }, Err(err))
            if err.to_string().contains(want) => {}
        (_, got) => bail!("[{mode:?}] RVM: unexpected result {got:?}"),
    }
    Ok(())
}

const MODES: [ExecutionMode; 2] = [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable];

fn check(modules: &[&str], entrypoint: &str, input: &str, strict: bool, expect: &Expect) -> Vec<String> {
    let label = if strict { "strict" } else { "non-strict" };
    let mut failures = Vec::new();
    let result = (|| {
        let input = Value::from_json_str(input)?;
        let mut engine = new_engine(modules, strict)?;
        engine.set_input(input);
        check_interpreter(expect, &engine.eval_rule(entrypoint.into()))
    })();
    if let Err(err) = result {
        failures.push(format!("{label}: {err:#}"));
    }
    for mode in MODES {
        let result = (|| {
            let input = Value::from_json_str(input)?;
            let mut vm = new_vm(modules, entrypoint, mode, strict)?;
            check_rvm(expect, &eval_vm(&mut vm, mode, entrypoint, &input)?, mode)
        })();
        if let Err(err) = result {
            failures.push(format!("{label}: {err:#}"));
        }
    }
    failures
}

#[test]
fn strict_builtin_errors_match_interpreter() {
    let mut failures = Vec::new();
    for case in cases() {
        for (strict, expect) in [(true, &case.strict), (false, &case.non_strict)] {
            for failure in check(&[case.module], case.entrypoint, case.input, strict, expect) {
                failures.push(format!("{}: {failure}", case.name));
            }
        }
    }

    // Reading the whole package evaluates the failing rule as well.
    let modules = [PACKAGE_READ, PACKAGE_READER];
    for (input, strict, expect) in [
        (V_BAD, true, Expect::Error(COUNT_ERROR)),
        (V_BAD, false, Expect::Value(r#"{"y": 1}"#)),
        (V_OK, true, Expect::Value(r#"{"y": 1, "z": 2}"#)),
    ] {
        for failure in check(&modules, "data.query.all", input, strict, &expect) {
            failures.push(format!("package read: {failure}"));
        }
    }

    assert!(
        failures.is_empty(),
        "{} strict builtin error checks failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// A strict error aborts one evaluation only. The same VM must then evaluate
/// other inputs normally, and after switching strict mode off it must absorb
/// the same failure again.
#[test]
fn strict_builtin_error_does_not_poison_later_evaluations() -> Result<()> {
    let steps = [
        (true, V_BAD, Expect::Error(COUNT_ERROR)),
        (true, V_OK, Expect::Value("2")),
        (true, V_BAD, Expect::Error(COUNT_ERROR)),
        (false, V_BAD, Expect::Value("0")),
        (false, V_OK, Expect::Value("2")),
        (true, V_BAD, Expect::Error(COUNT_ERROR)),
    ];
    let mut failures = Vec::new();
    for mode in MODES {
        let mut vm = new_vm(&[DEFAULT], Y, mode, true)?;
        for (step, (strict, input, expect)) in steps.iter().enumerate() {
            vm.set_strict_builtin_errors(*strict);
            let result = eval_vm(&mut vm, mode, Y, &Value::from_json_str(input)?)
                .and_then(|got| check_rvm(expect, &got, mode));
            if let Err(err) = result {
                failures.push(format!("step {step}: {err:#}"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} reuse steps failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
    Ok(())
}
