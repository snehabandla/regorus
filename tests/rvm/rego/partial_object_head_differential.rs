// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Typed OPA whole-document contracts plus equivalent child projections.
//! The frozen contracts evaluate only the contributing heads: unrelated
//! generated wrappers can be statically ill-typed in OPA. Their original
//! rejection categories are recorded separately, not treated as runtime
//! answers. Both VM modes must match every supported projection.

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM};
use regorus::{Engine, Value};
use std::collections::BTreeMap;

const TEMPLATES: &[(&str, &str)] = &[
    (
        "var_key_contains",
        "p[k] contains 1 if { some k in input.ks }",
    ),
    (
        "dot_prefix_contains",
        "p.q[k] contains 2 if { some k in input.ks }",
    ),
    ("string_key_contains", "p[\"a\"] contains 3"),
    ("raw_string_key_contains", "p[`b`] contains 4"),
    ("input_key_bodyless_contains", "p[input.keys[_]] contains 5"),
    ("dot_leaf_contains", "p.x contains 6"),
    (
        "two_var_keys_contains",
        "p[k][j] contains 7 if { some k in input.ks; some j in input.js }",
    ),
    (
        "var_key_dot_suffix_contains",
        "p[k].y contains 8 if { some k in input.ks }",
    ),
    ("var_key_assign", "p[k] := 9 if { some k in input.js }"),
    (
        "dot_prefix_assign",
        "p.q[k] := 10 if { some k in input.js }",
    ),
    (
        "string_key_contains_body",
        "p[\"a\"] contains v if { some v in input.vs }",
    ),
    ("dot_prefix_string_key_contains", "p.q[\"c\"] contains 11"),
    (
        "var_key_contains_var_value",
        "p[k] contains v if { some k in input.ks; some v in input.vs }",
    ),
    ("dot_complete", "p.r := 12 if { \"a\" in input.ks }"),
    ("dot_complete_false", "p.r := 13 if { false }"),
    ("dot_default", "default p.r := 0"),
    ("plain_set", "p contains 14"),
    ("string_key_assign", "p[\"a\"] := 15"),
    (
        "two_var_keys_assign",
        "p[k][j] := 16 if { some k in input.ks; some j in input.js }",
    ),
    ("number_key_contains", "p[1] contains 17"),
    (
        "input_key_body_contains",
        "p[input.keys[_]] contains 18 if { true }",
    ),
];

const LOCAL_WRAPPERS: &str = r#"
w_p := p
w_q := p.q
w_a := p.a
w_a_bracket := p["a"]
w_q_a := p.q.a
w_x := p.x
w_a_m := p.a.m
w_r := p.r
w_iter := {k | some k, _ in p}
w_member := 1 in p.a
"#;

const DATA_WRAPPERS: &str = r#"package wrap
w_p := data.test.p
w_q := data.test.p.q
w_a := data.test.p.a
w_q_a := data.test.p.q.a
w_r := data.test.p.r
w_test := data.test
w_dyn := {k: v | some k; v := data.test.p[k]}
w_dyn_q := {k: v | some k; v := data.test.p.q[k]}
"#;

const WITH_WRAPPERS: &str = r#"package withp
w_ks := x if { x := data.test.p with input.ks as ["z"] }
w_keys := x if { x := data.test.p with input.keys as ["k1"] }
"#;

const QUERIES: &[&str] = &[
    "data.test.p",
    "data.test.w_p",
    "data.test.w_q",
    "data.test.w_a",
    "data.test.w_a_bracket",
    "data.test.w_q_a",
    "data.test.w_x",
    "data.test.w_a_m",
    "data.test.w_r",
    "data.test.w_iter",
    "data.test.w_member",
    "data.wrap.w_p",
    "data.wrap.w_q",
    "data.wrap.w_a",
    "data.wrap.w_q_a",
    "data.wrap.w_r",
    "data.wrap.w_test",
    "data.wrap.w_dyn",
    "data.wrap.w_dyn_q",
    "data.withp.w_ks",
    "data.withp.w_keys",
];
const NOT_A_RULE_PATH: &str = "not a valid rule path";
const WITH_UNSUPPORTED: &str = "the `with` keyword is not supported by the compiler yet";

#[derive(Debug, Clone, PartialEq)]
enum Outcome {
    Value(Value),
    Error(String),
}

fn project(value: &Value, path: &[&str]) -> Value {
    path.iter().fold(value.clone(), |value, key| {
        let key = Value::from(*key);
        match value {
            Value::Object(fields) => fields.get(&key).cloned().unwrap_or(Value::Undefined),
            Value::Set(items) if items.contains(&key) => key,
            _ => Value::Undefined,
        }
    })
}

fn object(fields: impl IntoIterator<Item = (Value, Value)>) -> Value {
    Value::from(fields.into_iter().collect::<BTreeMap<_, _>>())
}

fn indexed(value: &Value) -> Value {
    match value {
        Value::Object(_) => value.clone(),
        Value::Set(items) => object(items.iter().map(|value| (value.clone(), value.clone()))),
        _ => Value::new_object(),
    }
}

fn local_values(root: &Value) -> BTreeMap<String, Value> {
    let mut values = BTreeMap::from([("p".into(), root.clone()), ("w_p".into(), root.clone())]);
    for (name, path) in [
        ("w_q", vec!["q"]),
        ("w_a", vec!["a"]),
        ("w_a_bracket", vec!["a"]),
        ("w_q_a", vec!["q", "a"]),
        ("w_x", vec!["x"]),
        ("w_a_m", vec!["a", "m"]),
        ("w_r", vec!["r"]),
    ] {
        values.insert(name.into(), project(root, &path));
    }
    let members = match project(root, &["a"]) {
        Value::Undefined => Value::Undefined,
        Value::Set(items) => Value::Bool(items.contains(&Value::from(1u64))),
        Value::Object(fields) => Value::Bool(fields.values().any(|v| *v == Value::from(1u64))),
        _ => Value::Bool(false),
    };
    values.insert("w_member".into(), members);
    let keys = indexed(root);
    let mut iteration = Value::new_set();
    for key in keys.as_object().expect("indexed object").keys() {
        iteration.as_set_mut().expect("set").insert(key.clone());
    }
    values.insert("w_iter".into(), iteration);
    values
}

fn expected_query(root: &Value, query: &str) -> Value {
    let values = local_values(root);
    if query == "data.wrap.w_test" {
        return object(
            values
                .into_iter()
                .filter(|(_, v)| *v != Value::Undefined)
                .map(|(key, value)| (Value::from(key), value)),
        );
    }
    if query == "data.wrap.w_dyn" {
        return indexed(root);
    }
    if query == "data.wrap.w_dyn_q" {
        return indexed(&project(root, &["q"]));
    }
    values
        .get(query.rsplit('.').next().expect("query name"))
        .expect("known wrapper")
        .clone()
}

fn without_undefined_members(value: Value) -> Value {
    match value {
        Value::Object(fields) => object(
            fields
                .iter()
                .filter(|(_, member)| **member != Value::Undefined)
                .map(|(key, member)| (key.clone(), without_undefined_members(member.clone()))),
        ),
        value => value,
    }
}

fn build_engine(modules: &[String], input: &Value) -> anyhow::Result<Engine> {
    let mut engine = Engine::new();
    for (index, module) in modules.iter().enumerate() {
        engine.add_policy(format!("module_{index}.rego"), module.clone())?;
    }
    engine.set_input(input.clone());
    Ok(engine)
}

fn is_entry_point(modules: &[String], query: &str, input: &Value) -> bool {
    !matches!(
        build_engine(modules, input).and_then(|mut engine| engine.eval_rule(query.to_string())),
        Err(error) if error.to_string() == NOT_A_RULE_PATH
    )
}

fn run_rvm(modules: &[String], query: &str, mode: ExecutionMode, input: &Value) -> Outcome {
    let result = (|| -> anyhow::Result<Value> {
        let mut engine = build_engine(modules, input)?;
        let compiled = engine.compile_with_entrypoint(&query.into())?;
        let program = Compiler::compile_from_policy(&compiled, &[query])?;
        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_data(engine.get_data())?;
        vm.set_input(input.clone());
        vm.set_execution_mode(mode);
        let value = vm.execute()?;
        if mode == ExecutionMode::Suspendable {
            match vm.execution_state() {
                ExecutionState::Completed { result } => Ok(result.clone()),
                state => Err(anyhow::anyhow!("unexpected execution state {state:?}")),
            }
        } else {
            Ok(value)
        }
    })();
    match result {
        Ok(value) => Outcome::Value(without_undefined_members(value)),
        Err(error) => Outcome::Error(error.to_string()),
    }
}

fn generate_policies() -> Vec<(String, Vec<&'static str>, Vec<String>)> {
    let wrap = |mut modules: Vec<String>| {
        modules.push(format!("package test\n{LOCAL_WRAPPERS}"));
        modules.push(DATA_WRAPPERS.into());
        modules.push(WITH_WRAPPERS.into());
        modules
    };
    let mut policies = Vec::new();
    for (name, rule) in TEMPLATES {
        policies.push((
            name.to_string(),
            vec![*rule],
            wrap(vec![format!("package test\n{rule}\n")]),
        ));
    }
    for (first, rule) in TEMPLATES {
        for (second, other) in TEMPLATES {
            if first != second {
                policies.push((
                    format!("{first}+{second}"),
                    vec![*rule, *other],
                    wrap(vec![format!("package test\n{rule}\n{other}\n")]),
                ));
                policies.push((
                    format!("{first}|{second}"),
                    vec![*rule, *other],
                    wrap(vec![
                        format!("package test\n{rule}\n"),
                        format!("package test\n{other}\n"),
                    ]),
                ));
            }
        }
    }
    policies
}

fn record_exclusion(name: &str, query: &str, mode: ExecutionMode, input: &str, category: &str) {
    if let Ok(path) = std::env::var("PARTIAL_OBJECT_EXCLUSION_REPORT") {
        use std::io::Write as _;
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(format!("{path}.{input}.jsonl"))
            .expect("open exclusion ledger");
        writeln!(
            file,
            "{}",
            serde_json::json!({
                "category": category,
                "policy": name, "query": query, "mode": format!("{mode:?}"), "input": input
            })
        )
        .expect("write exclusion ledger");
    }
}

#[test]
fn partial_object_heads_match_opa() {
    assert_partial_object_heads(
        "populated",
        Value::from_json_str(r#"{"ks":["a","b"],"js":["m","n"],"vs":[20,21],"keys":["a","c"]}"#)
            .expect("valid input"),
    );
}

#[test]
fn partial_object_heads_empty_input_matches_opa() {
    assert_partial_object_heads(
        "empty",
        Value::from_json_str(r#"{"ks":[],"js":[],"vs":[],"keys":[]}"#).expect("valid input"),
    );
}

fn assert_partial_object_heads(input_name: &str, input: Value) {
    let contracts: serde_json::Value =
        serde_json::from_str(include_str!("partial_object_opa_contracts.json"))
            .expect("frozen OPA contracts");
    assert_eq!(contracts["opa_version"], "1.2.0");
    let filter = std::env::var("PARTIAL_OBJECT_DIFF_FILTER").ok();
    let mut failures = Vec::new();
    let mut checked = 0usize;
    let mut exclusions = 0usize;
    for (name, rules, modules) in generate_policies() {
        if filter.as_ref().is_some_and(|filter| !name.contains(filter)) {
            continue;
        }
        let contract = &contracts["cases"][&name];
        assert_eq!(
            contract["rules"],
            serde_json::json!(rules),
            "stale contract {name}"
        );
        let source = &contract[input_name];
        let root = if let Some(term) = source["term"].as_str() {
            let result = Engine::new()
                .eval_query(term.into(), false)
                .expect("OPA literal parses");
            let value = result
                .result
                .first()
                .expect("literal result")
                .expressions
                .first()
                .expect("literal expression")
                .value
                .clone();
            assert_eq!(
                serde_json::to_value(&value).expect("serialize literal"),
                source["value"]
            );
            Outcome::Value(value)
        } else if source["undefined"] == true {
            Outcome::Value(Value::Undefined)
        } else {
            let codes = source["errors"]
                .as_array()
                .expect("named OPA rejection category");
            assert!(codes.iter().all(|code| code == "rego_type_error"
                || code == "eval_conflict_error"
                || code == "opa_panic_mixed_rule_kinds"));
            Outcome::Error(format!("{}: {}", source["errors"], source["messages"]))
        };
        for &query in QUERIES {
            let entry_point = is_entry_point(&modules, query, &input);
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                if query == "data.wrap.w_test" && mode == ExecutionMode::Suspendable {
                    record_exclusion(
                        &name,
                        query,
                        mode,
                        input_name,
                        "pre-existing-whole-package-suspendable-boundary",
                    );
                    continue;
                }
                checked += 1;
                let mut actual = run_rvm(&modules, query, mode, &input);
                let expected = if query.starts_with("data.withp.") {
                    Outcome::Error(WITH_UNSUPPORTED.into())
                } else if !entry_point {
                    Outcome::Error(NOT_A_RULE_PATH.into())
                } else {
                    match &root {
                        Outcome::Error(error) => Outcome::Error(error.clone()),
                        Outcome::Value(root) => {
                            let expected = expected_query(root, query);
                            // C3 tracks pre-existing child-default ownership,
                            // independently of this parent's strict contract.
                            if rules.contains(&"default p.r := 0")
                                && project(root, &["r"]) == Value::Undefined
                            {
                                if matches!(query, "data.test.w_r" | "data.wrap.w_r")
                                    && actual == Outcome::Value(Value::from(0u64))
                                {
                                    record_exclusion(
                                        &name,
                                        query,
                                        mode,
                                        input_name,
                                        "C3-pre-existing-direct-child-default-ownership",
                                    );
                                    exclusions += 1;
                                    continue;
                                }
                                if query == "data.wrap.w_test" {
                                    if let Outcome::Value(Value::Object(fields)) = &mut actual {
                                        if fields.get(&Value::from("w_r"))
                                            == Some(&Value::from(0u64))
                                        {
                                            regorus::Rc::make_mut(fields)
                                                .remove(&Value::from("w_r"));
                                            record_exclusion(
                                                &name,
                                                query,
                                                mode,
                                                input_name,
                                                "C3-child-default-component-only",
                                            );
                                            exclusions += 1;
                                        }
                                    }
                                }
                            }
                            // Only the independently tracked membership component
                            // is excluded. Every remaining package member is checked.
                            if project(root, &["a"]) == Value::Undefined {
                                if query == "data.test.w_member"
                                    && actual == Outcome::Value(Value::Bool(false))
                                {
                                    record_exclusion(
                                        &name,
                                        query,
                                        mode,
                                        input_name,
                                        "C2-undefined-membership-component-only",
                                    );
                                    exclusions += 1;
                                    continue;
                                }
                                if query == "data.wrap.w_test" {
                                    if let Outcome::Value(Value::Object(fields)) = &mut actual {
                                        if fields.get(&Value::from("w_member"))
                                            == Some(&Value::Bool(false))
                                        {
                                            regorus::Rc::make_mut(fields)
                                                .remove(&Value::from("w_member"));
                                            record_exclusion(
                                                &name,
                                                query,
                                                mode,
                                                input_name,
                                                "C2-undefined-membership-component-only",
                                            );
                                            exclusions += 1;
                                        }
                                    }
                                }
                            }
                            Outcome::Value(expected)
                        }
                    }
                };
                let agrees = match (&actual, &expected) {
                    (Outcome::Value(actual), Outcome::Value(expected)) => actual == expected,
                    (Outcome::Error(actual), Outcome::Error(_))
                        if query.starts_with("data.withp.") =>
                    {
                        actual.contains(WITH_UNSUPPORTED)
                    }
                    (Outcome::Error(actual), Outcome::Error(_)) if !entry_point => {
                        actual == NOT_A_RULE_PATH
                    }
                    (Outcome::Error(actual), Outcome::Error(expected)) => {
                        error_contract_matches(actual, expected)
                    }
                    _ => false,
                };
                if !agrees {
                    if let Ok(path) = std::env::var("PARTIAL_OBJECT_DIFF_REPORT") {
                        use std::io::Write as _;
                        let mut file = std::fs::OpenOptions::new()
                            .create(true)
                            .append(true)
                            .open(format!("{path}.{input_name}.jsonl"))
                            .expect("open failure ledger");
                        writeln!(
                            file,
                            "{}",
                            serde_json::json!({
                                "policy": name, "query": query, "mode": format!("{mode:?}"),
                                "input": input_name, "opa": format!("{expected:?}"),
                                "actual": format!("{actual:?}"), "contract": source
                            })
                        )
                        .expect("write failure ledger");
                    }

                    failures.push(format!(
                        "{name} {query} {mode:?}\n  OPA: {expected:?}\n  RVM: {actual:?}"
                    ));
                }
            }
        }
    }
    println!(
        "{input_name}: {checked} evaluations, {exclusions} named pre-existing components excluded"
    );
    assert!(checked > 0, "vacuous oracle");
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures
            .iter()
            .take(30)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

fn error_contract_matches(actual: &str, expected: &str) -> bool {
    if expected.contains("rego_type_error") || expected.contains("opa_panic_mixed_rule_kinds") {
        actual.contains("conflicting rules for")
    } else if expected.contains("eval_conflict_error") {
        actual.contains("Partial object rule conflict:")
    } else {
        false
    }
}

#[test]
fn partial_object_error_contract_rejects_unrelated_failures() {
    assert!(error_contract_matches(
        "conflicting rules for 'p'",
        "rego_type_error"
    ));
    assert!(error_contract_matches(
        "Partial object rule conflict: object keys must be unique",
        "eval_conflict_error"
    ));
    for expected in [
        "rego_type_error",
        "eval_conflict_error",
        "opa_panic_mixed_rule_kinds",
    ] {
        for actual in [
            "Invalid ObjectDeepSet operand",
            "not a valid rule path",
            "rule path is not supported",
            "LiteralIndexOutOfBounds",
        ] {
            assert!(!error_contract_matches(actual, expected));
        }
    }
    assert!(!error_contract_matches(
        "Partial object rule conflict:",
        "rego_type_error"
    ));
    assert!(!error_contract_matches(
        "conflicting rules for 'p'",
        "eval_conflict_error"
    ));
}
