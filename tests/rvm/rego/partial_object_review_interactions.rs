// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::Program;
use regorus::rvm::vm::{ExecutionMode, RegoVM};
use regorus::{Engine, Value};

fn compile(sources: &[String], query: &str) -> anyhow::Result<Program> {
    let mut engine = Engine::new();
    for (i, source) in sources.iter().enumerate() {
        engine.add_policy(format!("{i}.rego"), source.clone())?;
    }
    let policy = engine.compile_with_entrypoint(&query.into())?;
    Ok(Compiler::compile_from_policy(&policy, &[query])?
        .as_ref()
        .clone())
}

fn run(source: &str, input: &str, mode: ExecutionMode) -> anyhow::Result<Value> {
    let program = compile(&[format!("package test\n{source}")], "data.test.main")?;
    execute(program, input, mode)
}

fn execute(program: Program, input: &str, mode: ExecutionMode) -> anyhow::Result<Value> {
    let mut vm = RegoVM::new();
    vm.load_program(program.into());
    vm.set_execution_mode(mode);
    vm.set_input(Value::from_json_str(input)?);
    Ok(vm.execute()?)
}

fn modes() -> [ExecutionMode; 2] {
    [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable]
}

#[test]
fn review_whole_function_namespace() {
    for mode in modes() {
        for source in [
            "lib.f(x) := x+1\nlib.g := 5\nlib.h := 6\nmain := lib",
            "lib.h := 6\nlib.g := 5\nlib.f(x) := x+1\nmain := lib",
        ] {
            assert_eq!(
                run(source, "{}", mode).unwrap(),
                Value::from_json_str(r#"{"g":5,"h":6}"#).unwrap()
            );
        }
        assert_eq!(
            run(
                "lib.f(x) := x+1\nlib.g := 5 if { input.enabled }\nmain := lib",
                r#"{"enabled":false}"#,
                mode
            )
            .unwrap(),
            Value::new_object()
        );
    }
}

#[test]
fn review_default_only_function_namespace() {
    for mode in modes() {
        assert_eq!(
            run(
                "lib.f(x) := x+1\ndefault lib.g := 1\nmain := [lib,lib]",
                "{}",
                mode
            )
            .unwrap(),
            Value::from_json_str(r#"[{"g":1},{"g":1}]"#).unwrap()
        );
        assert_eq!(
            run("default p := 7\nmain := p", "{}", mode).unwrap(),
            Value::from(7u64)
        );
    }
}

#[test]
fn review_cross_package_definition_context() {
    for mode in modes() {
        for reverse in [false, true] {
            let mut sources = vec![
                "package a.b\np.r := 1\ny := 100".to_owned(),
                "package a\ny := 7\nb.p.q := y if { input.enabled }".to_owned(),
                "package entry\nmain := data.a.b.p".to_owned(),
            ];
            if reverse {
                sources.reverse();
            }
            let program = compile(&sources, "data.entry.main").unwrap();
            for (input, expected) in [
                (r#"{"enabled":true}"#, r#"{"q":7,"r":1}"#),
                (r#"{"enabled":false}"#, r#"{"r":1}"#),
            ] {
                assert_eq!(
                    execute(program.clone(), input, mode).unwrap(),
                    Value::from_json_str(expected).unwrap()
                );
            }
        }
    }
}

#[test]
fn review_dynamic_variable_static_child_collision() {
    for mode in modes() {
        for name in ["a", "k"] {
            let source = format!(
                "p[{name}].c := 1 if {{ some {name} in input.ks }}\np.a.d := 2\nmain := p.a"
            );
            for (input, expected) in [
                (r#"{"ks":["a"]}"#, r#"{"c":1,"d":2}"#),
                (r#"{"ks":["b"]}"#, r#"{"d":2}"#),
            ] {
                assert_eq!(
                    run(&source, input, mode).unwrap(),
                    Value::from_json_str(expected).unwrap()
                );
            }
        }
    }
}

#[test]
fn review_object_leaf_descendant_conflict() {
    for mode in modes() {
        for reverse in [false, true] {
            for leaf in [r#"{"x":1}"#, r#"{"b":2}"#] {
                let mut rules = [
                    format!("p[k] := {leaf} if {{ some k in input.ks }}"),
                    "p.a.b := 2".to_owned(),
                ];
                if reverse {
                    rules.reverse();
                }
                let source = format!("{}\n{}\nmain := p", rules[0], rules[1]);
                let error = run(&source, r#"{"ks":["a"]}"#, mode).unwrap_err();
                assert!(error.to_string().contains("conflicting values"), "{error}");
                let expected = if leaf == r#"{"x":1}"# {
                    r#"{"a":{"b":2},"z":{"x":1}}"#
                } else {
                    r#"{"a":{"b":2},"z":{"b":2}}"#
                };
                assert_eq!(
                    run(&source, r#"{"ks":["z"]}"#, mode).unwrap(),
                    Value::from_json_str(expected).unwrap()
                );
                assert_eq!(
                    run(&source, r#"{"ks":[]}"#, mode).unwrap(),
                    Value::from_json_str(r#"{"a":{"b":2}}"#).unwrap()
                );
            }
        }
        let program = compile(&[
            "package test\np[k] := {\"x\":1} if { some k in input.ks }\np.a.b := q.a.b\nq.a.b := 2\nmain := [q,p]".to_owned()
        ], "data.test.main").unwrap();
        let mut vm = RegoVM::new();
        vm.load_program(program.into());
        vm.set_execution_mode(mode);
        vm.set_input(Value::from_json_str(r#"{"ks":["a"]}"#).unwrap());
        assert!(vm
            .execute()
            .unwrap_err()
            .to_string()
            .contains("conflicting values"));
        for _ in 0..2 {
            vm.set_input(Value::from_json_str(r#"{"ks":["z"]}"#).unwrap());
            assert_eq!(
                vm.execute().unwrap(),
                Value::from_json_str(r#"[{"a":{"b":2}},{"a":{"b":2},"z":{"x":1}}]"#).unwrap()
            );
        }
    }
}

#[test]
fn review_static_leaf_prefix_rejected() {
    for enabled in ["true", "false"] {
        for reverse in [false, true] {
            let mut rules = [
                format!("p.a := 1 if {{ {enabled} }}"),
                "p.a.b contains 2".to_owned(),
            ];
            if reverse {
                rules.reverse();
            }
            let source = format!("package test\n{}\n{}\nmain := p", rules[0], rules[1]);
            assert!(compile(&[source], "data.test.main").is_err());
        }
    }
    for mode in modes() {
        assert_eq!(
            run("p.a := 1\np.b.c := 2\nmain := p", "{}", mode).unwrap(),
            Value::from_json_str(r#"{"a":1,"b":{"c":2}}"#).unwrap()
        );
    }
}

#[test]
fn review_native_float_literal_boundary() {
    for exponent in [63, 64] {
        let value = 2f64.powi(exponent);
        for value in [
            value,
            f64::from_bits(value.to_bits() - 1),
            f64::from_bits(value.to_bits() + 1),
        ] {
            let mut program = Program::new();
            program.literals = vec![Value::from(value)];
            let restored = Program::deserialize_json(&program.serialize_json().unwrap()).unwrap();
            assert_eq!(
                serde_json::to_string(&restored.literals).unwrap(),
                serde_json::to_string(&program.literals).unwrap()
            );
        }
    }
}
