// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::instructions::{InstructionData, ObjectDeepSetParams};
use regorus::rvm::program::Program;
use regorus::rvm::vm::{ExecutionMode, RegoVM};
use regorus::rvm::Instruction;
use regorus::{Engine, Value};

fn compile(source: &str, v0: bool) -> Program {
    let mut engine = Engine::new();
    engine.set_rego_v0(v0);
    engine
        .add_policy("test.rego".into(), format!("package test\n{source}"))
        .unwrap();
    let policy = engine
        .compile_with_entrypoint(&"data.test.main".into())
        .unwrap();
    Compiler::compile_from_policy(&policy, &["data.test.main"])
        .unwrap()
        .as_ref()
        .clone()
}

fn run(program: Program, mode: ExecutionMode, input: Value) -> anyhow::Result<Value> {
    let mut vm = RegoVM::new();
    vm.load_program(program.into());
    vm.set_execution_mode(mode);
    vm.set_input(input);
    Ok(vm.execute()?)
}

fn modes() -> [ExecutionMode; 2] {
    [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable]
}

#[test]
fn review_function_namespace() {
    for mode in modes() {
        let program = compile(
            "lib.f(x) := x + 1\nlib.g := 5\nmain := [lib.g, data.test.lib.g, lib.f(3)]",
            false,
        );
        assert_eq!(
            run(program, mode, Value::new_object()).unwrap(),
            Value::from_json_str("[5,5,4]").unwrap()
        );
        let absent = compile(
            "lib.f(x) := x + 1\nlib.g := 5 if { false }\nmain := lib.g",
            false,
        );
        assert_eq!(
            run(absent, mode, Value::new_object()).unwrap(),
            Value::Undefined
        );
    }
}

#[test]
fn review_static_collision_and_undefined() {
    for mode in modes() {
        for value in [9u64, 15] {
            let source =
                format!("p[\"a\"] := 15\np[k] := {value} if {{ some k in input.keys }}\nmain := p");
            let program = compile(&source, false);
            let input = Value::from_json_str(r#"{"keys":["a"]}"#).unwrap();
            let result = run(program.clone(), mode, input);
            if value == 9 {
                assert!(result
                    .unwrap_err()
                    .to_string()
                    .contains("conflicting values"));
            } else {
                assert_eq!(
                    result.unwrap(),
                    Value::from_json_str(r#"{"a":15}"#).unwrap()
                );
            }
            assert_eq!(
                run(
                    program,
                    mode,
                    Value::from_json_str(r#"{"keys":["b"]}"#).unwrap()
                )
                .unwrap(),
                Value::from_json_str(&format!(r#"{{"a":15,"b":{value}}}"#)).unwrap()
            );
        }
    }
}

#[test]
fn review_undefined_static_contribution() {
    for mode in modes() {
        let undefined = compile("p[\"a\"] := input.value\nmain := count(p)", false);
        assert_eq!(
            run(undefined.clone(), mode, Value::new_object()).unwrap(),
            Value::from(0u64)
        );
        assert_eq!(
            run(
                undefined,
                mode,
                Value::from_json_str(r#"{"value":1}"#).unwrap()
            )
            .unwrap(),
            Value::from(1u64)
        );
    }
}

#[test]
fn review_object_default_leaf() {
    for mode in modes() {
        let program = compile(
            "default p.a := {\"x\":1}\np.a := input.value if { input.enabled }\nmain := p",
            false,
        );
        for (input, expected) in [
            (r#"{"enabled":true,"value":{"y":2}}"#, r#"{"a":{"y":2}}"#),
            (r#"{"enabled":true,"value":{}}"#, r#"{"a":{}}"#),
            (r#"{"enabled":false}"#, r#"{"a":{"x":1}}"#),
        ] {
            assert_eq!(
                run(program.clone(), mode, Value::from_json_str(input).unwrap()).unwrap(),
                Value::from_json_str(expected).unwrap()
            );
        }
        let nested = compile("default p.a.x := 1\np.a.y := 2\nmain := p", false);
        assert_eq!(
            run(nested, mode, Value::new_object()).unwrap(),
            Value::from_json_str(r#"{"a":{"x":1,"y":2}}"#).unwrap()
        );
    }
}

#[test]
fn review_legacy_set_child() {
    for mode in modes() {
        let program = compile("p.x { input.enabled }\nmain := p.x", true);
        assert_eq!(
            run(
                program.clone(),
                mode,
                Value::from_json_str(r#"{"enabled":true}"#).unwrap()
            )
            .unwrap(),
            Value::from("x")
        );
        assert_eq!(
            run(
                program,
                mode,
                Value::from_json_str(r#"{"enabled":false}"#).unwrap()
            )
            .unwrap(),
            Value::Undefined
        );
    }
}

#[test]
fn review_legacy_json() {
    let mut legacy: serde_json::Value =
        serde_json::from_str(&Program::new().serialize_json().unwrap()).unwrap();
    legacy["instruction_data"]
        .as_object_mut()
        .unwrap()
        .remove("object_deep_set_params");
    Program::deserialize_json(&legacy.to_string()).unwrap();
}

#[test]
fn review_json_typed_seed() {
    let program = compile("p[1] contains 17 if { false }\nmain := p", false);
    let restored = Program::deserialize_json(&program.serialize_json().unwrap()).unwrap();
    for mode in modes() {
        assert_eq!(
            run(restored.clone(), mode, Value::new_object()).unwrap(),
            run(program.clone(), mode, Value::new_object()).unwrap()
        );
    }
}

#[test]
fn review_parameter_table_exhaustion() {
    let mut data = InstructionData::new();
    for _ in 0..=usize::from(u16::MAX).saturating_add(1) {
        let _ = data.add_object_deep_set_params(ObjectDeepSetParams {
            obj: 0,
            keys: vec![1],
            value: 2,
            multi_value: false,
        });
    }
    assert_eq!(data.object_deep_set_params.len(), usize::from(u16::MAX) + 1);
}

#[test]
fn review_malformed_instruction_in_rule() {
    let program = compile("p[k] contains 1 if { k := \"a\" }\nmain := p", false);
    for mode in modes() {
        for corruption in 0..4 {
            let mut corrupted = program.clone();
            if corruption == 0 {
                for instruction in &mut corrupted.instructions {
                    if let Instruction::ObjectDeepSet { params_index } = instruction {
                        *params_index = u16::MAX;
                    }
                }
            } else {
                for params in &mut corrupted.instruction_data.object_deep_set_params {
                    match corruption {
                        1 => params.keys = vec![u8::MAX],
                        2 => params.value = u8::MAX,
                        _ => params.obj = params.value,
                    }
                }
            }
            assert!(
                run(corrupted, mode, Value::new_object()).is_err(),
                "malformed instruction succeeded: mode {mode:?}, corruption {corruption}"
            );
        }
        assert!(run(program.clone(), mode, Value::new_object()).is_ok());
    }
}

#[test]
fn review_unprintable_conflict_key() {
    let number = format!("1{}", "0".repeat(400));
    let bigint = Value::Number(number.parse().unwrap());
    let mut input = Value::new_object();
    input
        .as_object_mut()
        .unwrap()
        .insert(Value::from("key"), bigint.clone());
    for mode in modes() {
        let program = compile("p.a[input.key] := 1\np.a[input.key] := 2\nmain := p", false);
        assert!(run(program, mode, input.clone())
            .unwrap_err()
            .to_string()
            .contains("conflicting values"));
        let equal = compile("p.a[input.key] := 1\np.a[input.key] := 1\nmain := p", false);
        let result = run(equal, mode, input.clone()).unwrap();
        assert_eq!(
            result
                .as_object()
                .unwrap()
                .get(&Value::from("a"))
                .unwrap()
                .as_object()
                .unwrap()
                .get(&bigint),
            Some(&Value::from(1u64))
        );
    }
}
