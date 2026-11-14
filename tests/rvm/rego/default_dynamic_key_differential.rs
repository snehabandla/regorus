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
    /// Query, then input and the expected result (JSON or `undefined`) from
    /// OPA, optionally followed by `; <engine prefix>=<value>` pins that record
    /// a divergence of that engine which predates this behavior (e.g. the RVM
    /// does not support nested dynamic keys such as `p.q[k].s`).
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
child := p.r
"#],
        queries: &[
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
            (
                "data.probe.p.r",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
        ],
    },
    Case {
        name: "dyn_sibling_deeper",
        v0: false,
        modules: &[r#"package probe
p.q[k] := 1 if { some k in input.ks }
default p.r := 0
child := p.r
"#],
        queries: &[
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
            (
                "data.probe.p.r",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
        ],
    },
    Case {
        name: "static_key_rule_sibling_default",
        v0: false,
        modules: &[r#"package probe
p["a"] := 1 if { "a" in input.ks }
default p.r := 0
child := p.r
"#],
        queries: &[
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
            (
                "data.probe.p.r",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
        ],
    },
    Case {
        name: "contains_sibling",
        v0: false,
        modules: &[r#"package probe
p.q contains k if { some k in input.ks }
default p.r := 0
child := p.r
"#],
        queries: &[
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
            (
                "data.probe.p.r",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
        ],
    },
    Case {
        name: "v0_partial_set_sibling",
        v0: true,
        modules: &[r#"package probe
p.q[x] { x := input.ks[_] }
default p.r = 0
child := p.r
"#],
        queries: &[
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
            (
                "data.probe.p.r",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
        ],
    },
    Case {
        name: "dyn_two_levels_default_mid",
        v0: false,
        modules: &[r#"package probe
p.q[k].s := 1 if { some k in input.ks }
default p.q.r.s := 0
default p.t := 2
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
child := p.r
"#,
        ],
        queries: &[
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
            (
                "data.probe.p.r",
                &[
                    (r#"{"ks":[]}"#, r#"0"#),
                    (r#"{"ks":["a"]}"#, r#"0"#),
                    (r#"{"ks":["r"]}"#, r#"0"#),
                ],
            ),
        ],
    },
    Case {
        name: "sibling_defaults_no_dyn",
        v0: false,
        modules: &[r#"package probe
p.r := 5 if input.x
default p.r := 0
default p.s := 1
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
    Case {
        name: "r1_rule_reads_shadowed_default",
        v0: false,
        modules: &[r#"package probe
p[k] := 1 if some k in input.ks
default p.r := 0
p.s := x if { x := p.r }
"#],
        queries: &[(
            "data.probe.p.s",
            &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ],
        )],
    },
    Case {
        name: "r2_rule_tests_shadowed_default",
        v0: false,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks; k != "s" }
default p.r := 0
p.s := 7 if { p.r }
"#],
        queries: &[(
            "data.probe.p.s",
            &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"7"#),
            ],
        )],
    },
    Case {
        name: "t1_dyn_two_levels_default_mid",
        v0: false,
        modules: &[r#"package probe
p.q[k].s := 1 if { some k in input.ks }
default p.q.r.s := 0
default p.t := 2
parent := p
child := p.q.r.s
t := p.t
"#],
        queries: &[
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1; rvm=undefined"#),
                ],
            ),
            (
                "data.probe.parent",
                &[
                    (
                        r#"{"ks":[]}"#,
                        r#"{"q":{},"t":2}; interpreter={"t":2}; rvm=undefined"#,
                    ),
                    (r#"{"ks":["a"]}"#, r#"{"q":{"a":{"s":1}},"t":2}; rvm=1"#),
                    (r#"{"ks":["r"]}"#, r#"{"q":{"r":{"s":1}},"t":2}; rvm=1"#),
                ],
            ),
            (
                "data.probe.p.q.r.s",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1; rvm=undefined"#),
                ],
            ),
        ],
    },
    Case {
        name: "t2_virtual_lookup",
        v0: false,
        modules: &[
            r#"package probe
p[k] := 1 if some k in input.ks
default p.r := 0
"#,
            r#"package q
y := data.probe[input.n].r
all := data.probe
"#,
        ],
        queries: &[(
            "data.q.y",
            &[
                (r#"{"ks":[],"n":"p"}"#, r#"undefined"#),
                (r#"{"ks":["r"],"n":"p"}"#, r#"1; rvm=undefined"#),
            ],
        )],
    },
    Case {
        name: "t3_data_chain_via_static_rule",
        v0: false,
        modules: &[r#"package probe
p[x] := {"t": 1} if some x in input.ks
p.r.s := 2 if input.y
default p.r.t := 0
a := data.probe.p.r.t
b := p.r.t
"#],
        queries: &[
            (
                "data.probe.a",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1"#),
                ],
            ),
            (
                "data.probe.b",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1"#),
                ],
            ),
        ],
    },
    Case {
        name: "t4_number_owner_string_default",
        v0: false,
        modules: &[r#"package probe
p[1][k] := 1 if some k in input.ks
default p["1"].s := 0
a := p["1"].s
b := p[1]
"#],
        queries: &[(
            "data.probe.a",
            &[(r#"{"ks":[]}"#, r#"0"#), (r#"{"ks":["s"]}"#, r#"0"#)],
        )],
    },
    Case {
        name: "t4b_bool_owner_string_default",
        v0: false,
        modules: &[r#"package probe
p[true][k] := 1 if some k in input.ks
default p["true"].s := 0
a := p["true"].s
"#],
        queries: &[(
            "data.probe.a",
            &[(r#"{"ks":[]}"#, r#"0"#), (r#"{"ks":["s"]}"#, r#"0"#)],
        )],
    },
    Case {
        name: "t5_number_key_redirect",
        v0: false,
        modules: &[r#"package probe
p[k] := {"s": 9} if some k in input.ks
default p[1].s := 0
a := p[1].s
"#],
        queries: &[
            (
                "data.probe.a",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":[1]}"#, r#"9"#),
                    (r#"{"ks":["1"]}"#, r#"undefined"#),
                ],
            ),
            (
                "data.probe.p.1.s",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":[1]}"#, r#"9; interpreter=undefined"#),
                    (r#"{"ks":["1"]}"#, r#"undefined; interpreter=9"#),
                ],
            ),
        ],
    },
    Case {
        name: "t6_mixed_owner",
        v0: false,
        modules: &[r#"package probe
p[k] := 1 if some k in input.ks
p.q := 2 if input.x
default p.r := 0
a := p.r
"#],
        queries: &[
            (
                "data.probe.a",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1"#),
                    (r#"{"ks":["r"],"x":true}"#, r#"1"#),
                ],
            ),
            (
                "data.probe.p.r",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1"#),
                    (r#"{"ks":["r"],"x":true}"#, r#"1"#),
                ],
            ),
        ],
    },
    Case {
        name: "t7_phantom_var_path",
        v0: false,
        modules: &[r#"package probe
p[k].s := 1 if some k in input.ks
default p.k := 0
a := p.k
"#],
        queries: &[
            (
                "data.probe.a",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["k"]}"#, r#"{"s":1}; rvm=1"#),
                    (r#"{"ks":["a"]}"#, r#"undefined; rvm=1"#),
                ],
            ),
            (
                "data.probe.p.k",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["k"]}"#, r#"{"s":1}; rvm=1"#),
                    (r#"{"ks":["a"]}"#, r#"undefined; rvm=1"#),
                ],
            ),
        ],
    },
    Case {
        name: "t8_import_alias",
        v0: false,
        modules: &[
            r#"package probe
p[k] := 1 if some k in input.ks
default p.r := 0
"#,
            r#"package q
import data.probe.p.r as pr
y := pr
"#,
        ],
        queries: &[(
            "data.q.y",
            &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ],
        )],
    },
    Case {
        name: "t9_order_twin",
        v0: false,
        modules: &[r#"package probe
default p.t := 2
default p.q.r.s := 0
p.q[k].s := 1 if { some k in input.ks }
t := p.t
child := p.q.r.s
"#],
        queries: &[
            (
                "data.probe.t",
                &[(r#"{"ks":[]}"#, r#"2"#), (r#"{"ks":["r"]}"#, r#"2"#)],
            ),
            (
                "data.probe.child",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["r"]}"#, r#"1; rvm=undefined"#),
                ],
            ),
            (
                "data.probe.p.t",
                &[(r#"{"ks":[]}"#, r#"2"#), (r#"{"ks":["r"]}"#, r#"2"#)],
            ),
        ],
    },
    // OPA rejects this policy (`p.q` conflicts with `p.q.r`); the expected
    // values are those without the default, which regorus falls back to.
    Case {
        name: "p3_mixed_subset",
        v0: false,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
p.q := {"r": 5} if input.x
default p.q.r := 0
a := p.q.r
b := data.probe.p.q.r
"#],
        queries: &[
            (
                "data.probe.a",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"],"x":true}"#, r#"5"#),
                ],
            ),
            (
                "data.probe.b",
                &[
                    (r#"{"ks":[]}"#, r#"undefined"#),
                    (r#"{"ks":["a"],"x":true}"#, r#"5"#),
                ],
            ),
        ],
    },
];

fn expected(text: &str, engine: &str) -> Result<Value> {
    let mut parts = text.split("; ");
    let mut text = parts.next().unwrap_or_default();
    for pin in parts {
        if let Some((prefix, value)) = pin.split_once('=') {
            if engine.starts_with(prefix) {
                text = value;
            }
        }
    }
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
                let results = match eval_all(case, query, &Value::from_json_str(input)?) {
                    Ok(results) => results,
                    Err(e) => {
                        failures.push(format!("{} {query} input={input}: {e:#}", case.name));
                        continue;
                    }
                };
                for (engine, got) in results {
                    let want = expected(want, engine)?;
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
