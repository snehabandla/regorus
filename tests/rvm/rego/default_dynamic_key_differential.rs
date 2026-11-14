// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Differential test for `default` rules beneath a dynamically keyed rule.
//!
//! Like OPA, a rule whose ref head has a dynamic key (`p[k] := 1`) owns its
//! whole extent: a `default` rule at or beneath it (`default p.r := 0`) is
//! ignored, so `p.r` is defined only when `p[k]` produces `r`. A default
//! beside a deeper dynamic rule (`p.q[k]`) or beside a constant key still
//! applies. The expected values were produced by OPA 1.2.0; each must match in
//! the interpreter and in both RVM execution modes.

use anyhow::Result;
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, RegoVM};
use regorus::{Engine, Value};

struct Case {
    name: &'static str,
    v0: bool,
    modules: &'static [&'static str],
    /// Query, then input and the expected result (JSON or `undefined`).
    queries: &'static [(&'static str, &'static [(&'static str, &'static str)])],
}

const CASES: &[Case] = &[
    Case {
        name: "base",
        v0: false,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
parent := p
child := p.r
"#],
        queries: &[
            (
                "data.probe.parent",
                &[
                    (r#"{"ks":[]}"#, r#"{}"#),
                    (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                    (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
                ],
            ),
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1"#),
                ],
            ),
            (
                "data.probe.p.r",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1"#),
                ],
            ),
            (
                "data.probe.p",
                &[
                    (r#"{"ks":[]}"#, r#"{}"#),
                    (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                    (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
                ],
            ),
        ],
    },
    Case {
        name: "default_two_levels",
        v0: false,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r.s := 0
parent := p
child := p.r.s
"#],
        queries: &[
            (
                "data.probe.parent",
                &[
                    (r#"{"ks":[]}"#, r#"{}"#),
                    (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                    (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
                ],
            ),
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"undefined"#),
                ],
            ),
        ],
    },
    Case {
        name: "multi_module_pkg",
        v0: false,
        modules: &[
            r#"package probe
p[k] := 1 if { some k in input.ks }
parent := p
child := p.r
"#,
            r#"package probe.p
default r := 0
"#,
        ],
        queries: &[
            (
                "data.probe.parent",
                &[
                    (r#"{"ks":[]}"#, r#"{}"#),
                    (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                    (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
                ],
            ),
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1"#),
                ],
            ),
            (
                "data.probe.p.r",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1"#),
                ],
            ),
        ],
    },
    Case {
        name: "multi_module_same_pkg",
        v0: false,
        modules: &[
            r#"package probe
p[k] := 1 if { some k in input.ks }
parent := p
child := p.r
"#,
            r#"package probe
default p.r := 0
"#,
        ],
        queries: &[(
            "data.probe.child",
            &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ],
        )],
    },
    Case {
        name: "default_first_module",
        v0: false,
        modules: &[
            r#"package probe
default p.r := 0
parent := p
child := p.r
"#,
            r#"package probe
p[k] := 1 if { some k in input.ks }
"#,
        ],
        queries: &[(
            "data.probe.child",
            &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ],
        )],
    },
    Case {
        name: "two_defaults_under_dyn",
        v0: false,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
default p.s := 1
parent := p
child := p.r
"#],
        queries: &[
            (
                "data.probe.parent",
                &[
                    (r#"{"ks":[]}"#, r#"{}"#),
                    (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                    (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
                ],
            ),
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1"#),
                ],
            ),
            (
                "data.probe.p.s",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"undefined"#),
                ],
            ),
        ],
    },
    Case {
        name: "dyn_deeper_default_under",
        v0: false,
        modules: &[r#"package probe
p.q[k] := 1 if { some k in input.ks }
default p.q.r := 0
parent := p
child := p.q.r
"#],
        queries: &[(
            "data.probe.child",
            &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ],
        )],
    },
    Case {
        name: "default_obj_value",
        v0: false,
        modules: &[r#"package probe
p[k] := {"v": 1} if { some k in input.ks }
default p.r := {"v": 0}
parent := p
child := p.r
"#],
        queries: &[
            (
                "data.probe.parent",
                &[
                    (r#"{"ks":[]}"#, r#"{}"#),
                    (r#"{"ks":["a"]}"#, r#"{"a":{"v":1}}"#),
                    (r#"{"ks":["r"]}"#, r#"{"r":{"v":1}}"#),
                ],
            ),
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"{"v":1}"#),
                ],
            ),
        ],
    },
    Case {
        name: "subpkg_local_ref",
        v0: false,
        modules: &[
            r#"package probe
p[k] := 1 if { some k in input.ks }
child := p.y
"#,
            r#"package probe.p
default r := 0
y := r
"#,
        ],
        queries: &[(
            "data.probe.child",
            &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ],
        )],
    },
    Case {
        name: "dyn_key_ref_lookup",
        v0: false,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
y := p[input.k]
"#],
        queries: &[(
            "data.probe.y",
            &[
                (r#"{"ks":[],"k":"r"}"#, r#"undefined"#),
                (r#"{"ks":["r"],"k":"r"}"#, r#"1"#),
                (r#"{"ks":["a"],"k":"a"}"#, r#"1"#),
            ],
        )],
    },
    Case {
        name: "dyn_key_lookup_var",
        v0: false,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
y := p[input.k]
z := v if { some k; v := p[k]; k == input.k }
"#],
        queries: &[
            (
                "data.probe.y",
                &[
                    (r#"{"ks":[],"k":"r"}"#, r#"undefined"#),
                    (r#"{"ks":["r"],"k":"r"}"#, r#"1"#),
                    (r#"{"ks":["a"],"k":"r"}"#, r#"undefined"#),
                ],
            ),
            (
                "data.probe.z",
                &[
                    (r#"{"ks":[],"k":"r"}"#, r#"undefined"#),
                    (r#"{"ks":["r"],"k":"r"}"#, r#"1"#),
                    (r#"{"ks":["a"],"k":"r"}"#, r#"undefined"#),
                ],
            ),
        ],
    },
    Case {
        name: "virtual_pkg_from_other",
        v0: false,
        modules: &[
            r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
"#,
            r#"package q
all := data.probe
child := data.probe.p.r
"#,
        ],
        queries: &[(
            "data.q.child",
            &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ],
        )],
    },
    Case {
        name: "static_rule_and_default",
        v0: false,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
p.r := 2 if input.x
default p.r := 0
parent := p
child := p.r
"#],
        queries: &[(
            "data.probe.child",
            &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":[],"x":true}"#, r#"2"#),
                (r#"{"ks":["a"],"x":true}"#, r#"2"#),
            ],
        )],
    },
    Case {
        name: "no_dynamic",
        v0: false,
        modules: &[r#"package probe
p.a := 1 if { "a" in input.ks }
default p.r := 0
parent := p
child := p.r
"#],
        queries: &[(
            "data.probe.child",
            &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ],
        )],
    },
    Case {
        name: "dyn_sibling_deeper",
        v0: false,
        modules: &[r#"package probe
p.q[k] := 1 if { some k in input.ks }
default p.r := 0
parent := p
child := p.r
"#],
        queries: &[(
            "data.probe.child",
            &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ],
        )],
    },
    Case {
        name: "static_key_rule_sibling_default",
        v0: false,
        modules: &[r#"package probe
p["a"] := 1 if { "a" in input.ks }
default p.r := 0
parent := p
child := p.r
"#],
        queries: &[(
            "data.probe.child",
            &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ],
        )],
    },
    Case {
        name: "contains_sibling",
        v0: false,
        modules: &[r#"package probe
p.q contains k if { some k in input.ks }
default p.r := 0
parent := p
child := p.r
"#],
        queries: &[(
            "data.probe.child",
            &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ],
        )],
    },
    Case {
        name: "v0_partial_set_sibling",
        v0: true,
        modules: &[r#"package probe
p.q[x] { x := input.ks[_] }
default p.r = 0
parent := p
child := p.r
"#],
        queries: &[(
            "data.probe.child",
            &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ],
        )],
    },
    Case {
        name: "dyn_two_levels_default_mid",
        v0: false,
        modules: &[r#"package probe
p.q[k].s := 1 if { some k in input.ks }
default p.q.r.s := 0
default p.t := 2
parent := p
child := p.q.r.s
t := p.t
"#],
        queries: &[(
            "data.probe.t",
            &[
                (r#"{"ks":[]}"#, r#"2"#),
                (r#"{"ks":["a"]}"#, r#"2"#),
                (r#"{"ks":["r"]}"#, r#"2"#),
            ],
        )],
    },
    Case {
        name: "dyn_in_other_pkg_deeper",
        v0: false,
        modules: &[
            r#"package probe.p
q[k] := 1 if { some k in input.ks }
"#,
            r#"package probe
default p.r := 0
parent := p
child := p.r
"#,
        ],
        queries: &[(
            "data.probe.child",
            &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ],
        )],
    },
    Case {
        name: "sibling_defaults_no_dyn",
        v0: false,
        modules: &[r#"package probe
p.r := 5 if input.x
default p.r := 0
default p.s := 1
parent := p
child := p.r
"#],
        queries: &[
            (
                "data.probe.child",
                &[(r#"{}"#, r#"0"#), (r#"{"x":true}"#, r#"5"#)],
            ),
            (
                "data.probe.p.s",
                &[(r#"{}"#, r#"1"#), (r#"{"x":true}"#, r#"1"#)],
            ),
        ],
    },
];

fn expected(text: &str) -> Result<Value> {
    if text == "undefined" {
        Ok(Value::Undefined)
    } else {
        Value::from_json_str(text)
    }
}

fn eval_all(case: &Case, query: &str, input: &Value) -> Result<Vec<(&'static str, Value)>> {
    let mut engine = Engine::new();
    engine.set_rego_v0(case.v0);
    for (i, module) in case.modules.iter().enumerate() {
        engine.add_policy(format!("m{i}.rego"), (*module).into())?;
    }
    engine.set_input(input.clone());
    let mut results = vec![("interpreter", engine.eval_rule(query.into())?)];
    for (label, mode) in [
        ("rvm run-to-completion", ExecutionMode::RunToCompletion),
        ("rvm suspendable", ExecutionMode::Suspendable),
    ] {
        let compiled = engine.compile_with_entrypoint(&query.into())?;
        let program = Compiler::compile_from_policy(&compiled, &[query])?;
        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_input(input.clone());
        vm.set_execution_mode(mode);
        results.push((label, vm.execute()?));
    }
    Ok(results)
}

#[test]
fn default_beneath_dynamic_key_matches_opa() -> Result<()> {
    let mut failures = Vec::new();
    for case in CASES {
        for (query, rows) in case.queries {
            for (input, want) in *rows {
                let want = expected(want)?;
                let results = match eval_all(case, query, &Value::from_json_str(input)?) {
                    Ok(results) => results,
                    Err(e) => {
                        failures.push(format!("{} {query} input={input}: {e:#}", case.name));
                        continue;
                    }
                };
                for (engine, got) in results {
                    if got != want {
                        failures.push(format!(
                            "{} {query} input={input} {engine}: got {got}, want {want}",
                            case.name
                        ));
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    Ok(())
}
