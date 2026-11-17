// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Alias path grammar and parsed alias catalog regressions.

#![allow(clippy::unwrap_used)]

use super::{
    denormalizer, normalizer, path,
    types::{PrecomputedRemap, PrecomputedReverseRemap, ResolvedEntry, VersionedAggregates},
    AliasRegistry,
};
use crate::Value;
use alloc::string::{String, ToString as _};
use alloc::vec;
use alloc::vec::Vec;
use serde_json::{json, Value as Json};

fn registry(aliases: &[(&str, &str)]) -> AliasRegistry {
    let entries: Vec<_> = aliases
        .iter()
        .map(|(short, arm)| json!({"name": alloc::format!("Test/widgets/{short}"), "defaultPath": arm}))
        .collect();
    let mut registry = AliasRegistry::new();
    registry
        .load_from_json(
            &json!([{
                "namespace": "Test",
                "resourceTypes": [{"resourceType": "widgets", "aliases": entries}]
            }])
            .to_string(),
        )
        .unwrap();
    registry
}

fn keys(text: &str) -> Option<Vec<String>> {
    path::parse(text)?
        .segments
        .into_iter()
        .map(|segment| match segment {
            path::Segment::Key(key) => Some(key.to_string()),
            _ => None,
        })
        .collect()
}

fn cases() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("['ab']", vec!["ab"]),
        ("[ab]", vec!["ab"]),
        ("[ ab ]", vec!["ab"]),
        ("[\"ab\"]", vec!["ab"]),
        ("['a.b']", vec!["a.b"]),
        ("['a[b]c']", vec!["a[b]c"]),
        ("['a[*]']", vec!["a[*]"]),
        ("['[*].properties.fake']", vec!["[*].properties.fake"]),
        ("['a].b']", vec!["a].b"]),
        ("['a'b']", vec!["a'b"]),
        ("['a' x].b']", vec!["a' x].b"]),
        ("[ ' ab ' \t]", vec![" ab "]),
        ("['a\\b']", vec!["a\\b"]),
        ("['é.中[*]']", vec!["é.中[*]"]),
        ("[\"'ab'\"]", vec!["'ab'"]),
        ("['123']", vec!["123"]),
        ("['Ab']", vec!["Ab"]),
        ("['ab'].nested[child]", vec!["ab", "nested", "child"]),
        ("[outer]['a.b'][leaf]", vec!["outer", "a.b", "leaf"]),
    ]
}

#[test]
fn bracket_keys_parse() {
    for (suffix, expected) in cases() {
        let mut expected: Vec<String> = expected.into_iter().map(String::from).collect();
        expected.insert(0, "renamed".into());
        let text = alloc::format!("renamed{suffix}");
        assert_eq!(keys(&text), Some(expected), "{text}");
    }
}

#[test]
fn render_round_trips_keys() {
    for text in [
        "a.b",
        "a['b.c'][0][*].d",
        "a[\"it's]\"]",
        "a[' b ']",
        "['[*]'].x",
        "rules[*].it's",
        "a[\"'b'\"]",
    ] {
        let segments = path::parse(text).unwrap().segments;
        assert_eq!(
            path::parse(&path::render(&segments)).unwrap().segments,
            segments,
            "{text}"
        );
    }
}

#[test]
fn parser_discriminators() {
    for (text, wildcard) in [
        ("a[*]", true),
        ("a[ * ]", false),
        ("a['*']", false),
        ("a['[*]']", false),
    ] {
        let parsed = path::parse(text).unwrap();
        assert_eq!(
            parsed.segments.contains(&path::Segment::Wildcard),
            wildcard,
            "{text}"
        );
    }
    for text in [
        "a..b", "a[]", "a['']", "a[", "a[b]junk", "a.", "a]", "a[4096]",
    ] {
        assert!(path::parse(text).is_none(), "{text}");
    }
    assert_eq!(
        path::parse("a[4095]").unwrap().segments.last(),
        Some(&path::Segment::Index(path::MAX_INDEX))
    );
}

#[test]
fn grammar_matches_compiler_field_paths() {
    for (text, expected) in [
        (
            "a[ 0 ]",
            vec![path::Segment::Key("a".into()), path::Segment::Index(0)],
        ),
        (
            "a.[0]",
            vec![path::Segment::Key("a".into()), path::Segment::Index(0)],
        ),
        (
            "a[ * ]",
            vec![
                path::Segment::Key("a".into()),
                path::Segment::Key("*".into()),
            ],
        ),
        (
            "a. [0]",
            vec![path::Segment::Key("a".into()), path::Segment::Index(0)],
        ),
        (
            "a. [*]",
            vec![path::Segment::Key("a".into()), path::Segment::Wildcard],
        ),
        (" [0]", vec![path::Segment::Index(0)]),
        ("a. ", vec![path::Segment::Key("a".into())]),
    ] {
        assert_eq!(path::parse(text).unwrap().segments, expected, "{text}");
    }
    for text in ["a. .b", " ", "a[0] [1]", ". [0]"] {
        assert!(path::parse(text).is_none(), "{text}");
    }
    let at_limit = vec!["a"; path::MAX_SEGMENTS].join(".");
    assert_eq!(
        path::parse(&at_limit).unwrap().segments.len(),
        path::MAX_SEGMENTS
    );
    assert!(path::parse(&(at_limit.clone() + ".a")).is_none());
    assert!(path::parse(&(at_limit + "[0]")).is_none());
}

#[test]
fn parts_split_only_real_wildcards() {
    let parsed = path::parse("a['[*].b'][*].c[*]").unwrap();
    let render = |parts: Vec<path::Part<'_>>| -> Vec<String> {
        parts
            .iter()
            .map(|part| path::render(part.segments))
            .collect()
    };
    assert_eq!(render(parsed.parts()), vec!["a['[*].b']", "c", ""]);
    assert_eq!(render(parsed.element_parts()), vec!["a['[*].b']", "c"]);
    assert_eq!(
        render(path::parse("[*]").unwrap().element_parts()),
        vec![""]
    );
}

#[test]
fn bracket_alias_wildcard_classification() {
    for (short, expected) in [
        ("renamed['a[*]']", false),
        ("renamed['[*].properties.fake']", false),
        ("renamed[\"a[*]b\"]", false),
        ("renamed['a' [*]' ]", false),
        ("renamed[*]", true),
        ("renamed['a[*]'][*].leaf", true),
        ("renamed['a[*]'].*", false),
    ] {
        let entry = ResolvedEntry::new(
            short.to_string(),
            "properties.original".to_string(),
            vec![],
            None,
        );
        assert_eq!(entry.is_wildcard, expected, "{short}");
    }
}

#[test]
fn bracket_rendered_leaves_are_remapped() {
    // Element remaps navigate parsed paths, so leaves that need a bracket
    // subscript move like dotted ones.
    let registry = registry(&[("rules[*]['a.b']", "properties.rules[*]['X.y']")]);
    let aggregates = &registry.get("Test/widgets").unwrap().default_aggregates;
    assert_eq!(
        aggregates.element_remaps,
        vec![PrecomputedRemap {
            array_chain: vec![vec!["rules".into()]],
            source_field: "['x.y']".into(),
            target_field: "['a.b']".into(),
        }]
    );
    assert_eq!(
        aggregates.reverse_element_remaps,
        vec![PrecomputedReverseRemap {
            array_chain: vec![vec!["rules".into()]],
            source_field: "['a.b']".into(),
            target_field: "['X.y']".into(),
            cleanup_field: "['a.b']".into(),
        }]
    );

    for (alias, arm, short) in [
        (
            ("rules[*]['a.b']", "properties.rules[*]['X.y']"),
            json!({"X.y": 1}),
            json!({"a.b": 1}),
        ),
        (
            ("rules[*]['a.b']", "properties.rules[*].xy"),
            json!({"xy": 1}),
            json!({"a.b": 1}),
        ),
        (
            ("rules[*].xy", "properties.rules[*]['a.b']"),
            json!({"a.b": 1}),
            json!({"xy": 1}),
        ),
        (
            ("rules[*]['a[b]']", "properties.rules[*].xy"),
            json!({"xy": 1}),
            json!({"a[b]": 1}),
        ),
        (
            ("rules[*].xs[0]", "properties.rules[*].ys[0]"),
            json!({"ys": [1]}),
            // An indexed source is copied: other aliases may read the array.
            json!({"ys": [1], "xs": [1]}),
        ),
    ] {
        let aliases = [alias];
        assert_eq!(
            normalized(&aliases, json!({"rules": [arm.clone(), {"other": 2}]})),
            Value::from(json!({"type": "Test/widgets", "rules": [short.clone(), {"other": 2}]})),
            "{alias:?}"
        );
        assert_eq!(
            denormalized(&aliases, json!({"rules": [short, {"other": 2}]})),
            Value::from(json!({"properties": {"rules": [arm, {"other": 2}]}})),
            "{alias:?}"
        );
    }
}

#[test]
fn quote_characters_stay_dotted() {
    assert_eq!(
        path::render(&path::parse("rules.it's.say\"hi\"").unwrap().segments),
        "rules.it's.say\"hi\""
    );
    let aliases = [("rules[*].x", "properties.rules[*].it's")];
    assert_eq!(
        normalized(&aliases, json!({"rules": [{"it's": 1}]})),
        Value::from(json!({"type": "Test/widgets", "rules": [{"x": 1}]}))
    );
    assert_eq!(
        denormalized(&aliases, json!({"rules": [{"x": 1}]})),
        Value::from(json!({"properties": {"rules": [{"it's": 1}]}}))
    );
}

#[test]
fn flattened_array_quoted_properties_is_the_wrapper() {
    // `x` makes `rules` a flattened sub-resource array, so the quoted
    // `['properties']` in `y` names the same wrapper that normalization lifts.
    let aliases = [
        ("rules[*].x", "properties.rules[*].properties.x"),
        ("rules[*].y", "properties.rules[*]['properties'].y"),
    ];
    assert_eq!(sub_resource_arrays(&aliases), vec!["rules"]);
    assert_eq!(
        registry(&aliases)
            .get("Test/widgets")
            .unwrap()
            .default_aggregates,
        VersionedAggregates::default()
    );
    assert_eq!(
        normalized(
            &aliases,
            json!({"rules": [{"name": "n", "properties": {"x": 1, "y": 2}}]})
        ),
        Value::from(json!({"type": "Test/widgets", "rules": [{"name": "n", "x": 1, "y": 2}]}))
    );
    assert_eq!(
        denormalized(&aliases, json!({"rules": [{"name": "n", "x": 1, "y": 2}]})),
        Value::from(
            json!({"properties": {"rules": [{"name": "n", "properties": {"x": 1, "y": 2}}]}})
        )
    );
    // An element with only `y` is still re-wrapped.
    assert_eq!(
        denormalized(&aliases, json!({"rules": [{"name": "n", "y": 2}]})),
        Value::from(json!({"properties": {"rules": [{"name": "n", "properties": {"y": 2}}]}}))
    );
}

#[test]
fn flattened_wrapper_lookup_uses_the_full_array_name() {
    // The flattened array is named by every key in the chain: `x.y` for a
    // nested array and `a.rules` behind an object prefix.
    let nested = [
        (
            "x[*].y[*].z",
            "properties.x[*].properties.y[*].properties.z",
        ),
        (
            "x[*].y[*].w",
            "properties.x[*].properties.y[*]['properties'].w",
        ),
    ];
    let prefixed = [
        ("a.rules[*].x", "properties.a.rules[*].properties.x"),
        ("a.rules[*].y", "properties.a.rules[*]['properties'].y"),
    ];
    assert_eq!(sub_resource_arrays(&nested), vec!["x", "x.y"]);
    assert_eq!(sub_resource_arrays(&prefixed), vec!["a.rules"]);
    for aliases in [nested, prefixed] {
        assert_eq!(
            registry(&aliases)
                .get("Test/widgets")
                .unwrap()
                .default_aggregates,
            VersionedAggregates::default(),
            "{aliases:?}"
        );
    }
    assert_eq!(
        denormalized(&nested, json!({"x": [{"y": [{"z": 1, "w": 2}]}]})),
        Value::from(
            json!({"properties": {"x": [{"properties": {"y": [{"properties": {"z": 1, "w": 2}}]}}]}})
        )
    );
    assert_eq!(
        normalized(
            &prefixed,
            json!({"a": {"rules": [{"properties": {"x": 1, "y": 2}}]}})
        ),
        Value::from(json!({"type": "Test/widgets", "a": {"rules": [{"x": 1, "y": 2}]}}))
    );
}

#[test]
fn quoted_wildcard_text_is_not_an_array() {
    let registry = registry(&[("rules['[*].x'].leaf", "properties.rules['[*].x'].other")]);
    let resolved = registry.get("Test/widgets").unwrap();
    assert!(!resolved.entries.values().any(|entry| entry.is_wildcard));
    assert!(resolved.sub_resource_arrays.is_empty());
    assert_eq!(resolved.default_aggregates, VersionedAggregates::default());
}

#[test]
fn equivalent_bracket_spellings_do_not_rename() {
    let same = registry(&[
        ("rules[*].x", "properties['rules'][*].x"),
        ("other[*].Leaf", "properties.other[*]['leaf']"),
    ]);
    assert_eq!(
        same.get("Test/widgets").unwrap().default_aggregates,
        VersionedAggregates::default()
    );
    let renamed = registry(&[("rules[*].x", "properties['rulesV2'][*].x")]);
    assert_eq!(
        renamed
            .get("Test/widgets")
            .unwrap()
            .default_aggregates
            .array_renames_normalize,
        vec![("rulesv2".to_string(), "rules".to_string())]
    );
}

#[test]
fn quoted_keys_restore_casing() {
    let registry = registry(&[("a['Mixed.Key']", "properties.a['Mixed.Key']")]);
    let restored = denormalizer::denormalize_with_aliases(
        &Value::from(json!({"unaliased": {"mixed.key": 7}})),
        registry.get("Test/widgets"),
        None,
    );
    assert_eq!(
        restored,
        Value::from(json!({"properties": {"unaliased": {"Mixed.Key": 7}}}))
    );
    // Unquoted, the same text names two keys; neither restores the dotted literal.
    assert_eq!(
        denormalized(
            &[("a.Mixed.Key", "properties.a.Mixed.Key")],
            json!({"unaliased": {"mixed.key": 7, "mixed": 1}})
        ),
        Value::from(json!({"properties": {"unaliased": {"mixed.key": 7, "Mixed": 1}}}))
    );
}

fn normalized(aliases: &[(&str, &str)], properties: serde_json::Value) -> Value {
    let registry = registry(aliases);
    normalizer::normalize_with_aliases(
        &Value::from(json!({"type": "Test/widgets", "properties": properties})),
        registry.get("Test/widgets"),
        None,
    )
}

fn denormalized(aliases: &[(&str, &str)], value: serde_json::Value) -> Value {
    let registry = registry(aliases);
    denormalizer::denormalize_with_aliases(&Value::from(value), registry.get("Test/widgets"), None)
}

fn sub_resource_arrays(aliases: &[(&str, &str)]) -> Vec<String> {
    registry(aliases)
        .get("Test/widgets")
        .unwrap()
        .sub_resource_arrays
        .iter()
        .cloned()
        .collect()
}

#[test]
fn quoted_properties_leaf_is_not_the_wrapper() {
    let quoted = [(
        "rules[*]['properties'].x",
        "properties.rules[*]['properties'].x",
    )];
    assert_eq!(
        normalized(
            &quoted,
            json!({"rules": [{"properties": {"x": 1}, "x": 2}]})
        ),
        Value::from(json!({"type": "Test/widgets", "rules": [{"properties": {"x": 1}, "x": 2}]}))
    );
    assert!(sub_resource_arrays(&quoted).is_empty());
    assert_eq!(
        registry(&quoted)
            .get("Test/widgets")
            .unwrap()
            .default_aggregates,
        VersionedAggregates::default()
    );

    let wrapped = [("rules[*].x", "properties.rules[*].properties.x")];
    assert_eq!(
        normalized(&wrapped, json!({"rules": [{"properties": {"x": 1}}]})),
        Value::from(json!({"type": "Test/widgets", "rules": [{"x": 1}]}))
    );
    assert_eq!(sub_resource_arrays(&wrapped), vec!["rules"]);
}

#[test]
fn properties_wrapper_is_case_insensitive() {
    for arm in [
        "Properties.x[*].Properties.y",
        "properties.x[*].properties.y",
    ] {
        let aliases = [("x[*].y", arm)];
        assert_eq!(sub_resource_arrays(&aliases), vec!["x"], "{arm}");
        assert_eq!(
            normalized(&aliases, json!({"x": [{"Properties": {"y": 1}}]})),
            Value::from(json!({"type": "Test/widgets", "x": [{"y": 1}]})),
            "{arm}"
        );
        assert_eq!(
            denormalized(&aliases, json!({"x": [{"y": 1, "name": "n"}]})),
            Value::from(json!({"properties": {"x": [{"name": "n", "properties": {"y": 1}}]}})),
            "{arm}"
        );
    }
}

#[test]
fn sub_resource_arrays_use_parsed_names() {
    for (aliases, expected) in [
        (
            vec![("['Rules'][*].x", "properties['Rules'][*].properties.x")],
            vec!["rules"],
        ),
        (
            vec![("a.[*].b", "properties.a.[*].properties.b")],
            vec!["a"],
        ),
        (
            vec![(
                "x[*].y[*].z",
                "properties.x[*].properties.y[*].properties.z",
            )],
            vec!["x", "x.y"],
        ),
        (vec![("x[*]", "properties.x[*].properties.y[*]")], vec![]),
        (vec![("x[*]", "properties.x[*]")], vec![]),
        (
            vec![("a[*][*].b", "properties.a[*][*].properties.b")],
            vec![],
        ),
        (
            vec![("a['b.c'][*].d", "properties.a['b.c'][*].properties.d")],
            vec![],
        ),
    ] {
        assert_eq!(sub_resource_arrays(&aliases), expected, "{aliases:?}");
    }
}

#[test]
fn trailing_wildcard_alias_keeps_element_wrapper() {
    assert_eq!(
        normalized(
            &[("x[*]", "properties.x[*].properties.y[*]")],
            json!({"x": [{"properties": {"y": [1]}, "z": 2}]})
        ),
        Value::from(json!({"type": "Test/widgets", "x": [{"properties": {"y": [1]}, "z": 2}]}))
    );
}

#[test]
fn unquoted_keys_take_casing_priority() {
    let aliases = [
        ("config['Tier']", "properties.config['Tier']"),
        ("tier", "properties.tier"),
    ];
    assert_eq!(
        denormalized(&aliases, json!({"tier": "basic", "other": {"tier": 1}})),
        Value::from(json!({"properties": {"tier": "basic", "other": {"tier": 1}}}))
    );
    assert_eq!(
        denormalized(&aliases[..1], json!({"other": {"tier": 1}})),
        Value::from(json!({"properties": {"other": {"Tier": 1}}}))
    );
}

#[test]
fn unparseable_paths_are_inert() {
    // An unparseable short name keeps the textual `[*]` classification, so it
    // never takes the scalar path.
    for (short, wildcard) in [
        ("a[4096][*].b", true),
        ("a[4095][*].b", true),
        ("a[4096].b", false),
    ] {
        let entry = ResolvedEntry::new(short.to_string(), "properties.a".to_string(), vec![], None);
        assert_eq!(entry.is_wildcard, wildcard, "{short}");
    }
    assert_eq!(
        normalized(
            &[("a[4096][*].b", "properties.a")],
            json!({"a": [{"b": 1}]})
        ),
        Value::from(json!({"type": "Test/widgets", "a": [{"b": 1}]}))
    );
    // Unparseable paths still supply casing through dot-split segments.
    for (aliases, remaps, casing) in [
        ([("a..b[*].c", "properties.a.b[*].D")], 0, "D"),
        ([("a.b[*].c", "properties.a..b[*].D")], 0, "D"),
        ([("a.b[*].c", "properties.a.b[*].D")], 1, "D"),
    ] {
        let resolved = registry(&aliases);
        let resolved = resolved.get("Test/widgets").unwrap();
        assert_eq!(resolved.default_aggregates.element_remaps.len(), remaps);
        assert!(resolved.sub_resource_arrays.is_empty());
        let mut expected = serde_json::Map::new();
        expected.insert(casing.into(), json!(1));
        assert_eq!(
            denormalized(&aliases, json!({"unaliased": {"d": 1}})),
            Value::from(json!({"properties": {"unaliased": expected}})),
            "{aliases:?}"
        );
    }
}

#[test]
fn slash_wrapper_must_be_unquoted() {
    assert_eq!(
        sub_resource_arrays(&[("rules[*].x", "properties.rules[*].properties/x")]),
        vec!["rules"]
    );
    let quoted = [("rules[*].x", "properties.rules[*]['properties/foo'].x")];
    assert!(sub_resource_arrays(&quoted).is_empty());
    let plain = [("rules[*].x", "properties.rules[*].foo.x")];
    assert_eq!(
        normalized(
            &plain,
            json!({"rules": [{"properties": {"kept": 1}, "foo": {"x": 2}}]})
        ),
        Value::from(json!({
            "type": "Test/widgets",
            "rules": [{"properties": {"kept": 1}, "x": 2}]
        }))
    );
    // The quoted key is an ordinary element field: the leaf is remapped as
    // for a plain key and the element's `properties` is not flattened.
    let element = json!({"properties": {"kept": 1}, "properties/foo": {"x": 2}});
    assert_eq!(
        normalized(&quoted, json!({"rules": [element]})),
        Value::from(json!({
            "type": "Test/widgets",
            "rules": [{"properties": {"kept": 1}, "x": 2}]
        }))
    );
}

#[test]
fn bracket_sub_resource_envelope_matches_dotted() {
    let expected = Value::from(json!({
        "properties": {"Rules": [{"kind": "k", "properties": {"x": 1}}]}
    }));
    for aliases in [
        [
            ("['Rules'][*].kind", "properties['Rules'][*].kind"),
            ("['Rules'][*].x", "properties['Rules'][*].properties.x"),
        ],
        [
            ("Rules[*].kind", "properties.Rules[*].kind"),
            ("Rules[*].x", "properties.Rules[*].properties.x"),
        ],
    ] {
        assert_eq!(
            denormalized(&aliases, json!({"Rules": [{"kind": "k", "x": 1}]})),
            expected,
            "{aliases:?}"
        );
    }
}

#[test]
fn unparseable_arm_path_does_not_classify_envelope() {
    let valid = ("rules[*].x", "properties.rules[*].properties.x");
    for (sibling, expected) in [
        (
            ("rules[*].y", "properties.rules[*].y..z"),
            json!({"rules": [{"properties": {"x": 1, "y": 2}}]}),
        ),
        (
            ("rules[*].y", "properties.rules[*].y"),
            json!({"rules": [{"y": 2, "properties": {"x": 1}}]}),
        ),
    ] {
        assert_eq!(
            denormalized(&[valid, sibling], json!({"rules": [{"x": 1, "y": 2}]})),
            Value::from(json!({"properties": expected})),
            "{sibling:?}"
        );
    }
}

#[test]
fn nested_fields_classify_envelope_at_their_own_level() {
    let aliases = [
        ("rules[*].x", "properties.rules[*].properties.x"),
        ("rules[*].tags[*]", "properties.rules[*].tags[*]"),
        (
            "rules[*].items[*].name",
            "properties.rules[*].properties.items[*].name",
        ),
    ];
    assert_eq!(
        denormalized(
            &aliases,
            json!({"rules": [{"x": 1, "tags": ["t"], "items": [{"name": "n"}]}]})
        ),
        Value::from(json!({"properties": {"rules": [{
            "tags": ["t"],
            "properties": {"x": 1, "items": [{"name": "n"}]}
        }]}}))
    );
}

#[test]
fn unparseable_paths_supply_casing() {
    for alias in [
        ("x", "properties.items[5000].fooBar"),
        ("x", "properties.a..fooBar"),
        ("a..fooBar", "properties.x"),
    ] {
        assert_eq!(
            denormalized(&[alias], json!({"u": {"foobar": 1}})),
            Value::from(json!({"properties": {"u": {"fooBar": 1}}})),
            "{alias:?}"
        );
    }

    let mut registry = AliasRegistry::new();
    registry
        .load_from_json(
            &json!([{"namespace": "Test", "resourceTypes": [{"resourceType": "widgets", "aliases": [{
                "name": "Test/widgets/x",
                "defaultPath": "properties.x",
                "paths": [{"path": "properties.b..fooBar", "apiVersions": ["2024-01-01"]}]
            }]}]}])
            .to_string(),
        )
        .unwrap();
    assert_eq!(
        denormalizer::denormalize_with_aliases(
            &Value::from(json!({"u": {"foobar": 1}})),
            registry.get("Test/widgets"),
            None
        ),
        Value::from(json!({"properties": {"u": {"fooBar": 1}}}))
    );
}

#[test]
fn unparseable_path_casing_beats_quoted_keys() {
    let aliases = [
        ("config['Tier']", "properties.config['Tier']"),
        ("y", "properties.a..tier"),
    ];
    assert_eq!(
        denormalized(&aliases, json!({"other": {"tier": 1}})),
        Value::from(json!({"properties": {"other": {"tier": 1}}}))
    );
}

#[test]
fn indexed_properties_is_not_a_wrapper() {
    let indexed = [("a[*].x", "properties.a[*].properties[0].x")];
    assert!(sub_resource_arrays(&indexed).is_empty());
    // The indexed `properties` is an ordinary element field: its value is
    // copied to the alias leaf and written back by index.
    assert_eq!(
        normalized(&indexed, json!({"a": [{"properties": [{"x": 1}]}]})),
        Value::from(json!({"type": "Test/widgets", "a": [{"properties": [{"x": 1}], "x": 1}]}))
    );
    assert_eq!(
        denormalized(&indexed, json!({"a": [{"x": 1}]})),
        Value::from(json!({"properties": {"a": [{"properties": [{"x": 1}]}]}}))
    );

    let wrapped = [("a[*].x", "properties.a[*].properties.x")];
    assert_eq!(sub_resource_arrays(&wrapped), vec!["a"]);
}

#[test]
fn short_name_properties_supplies_casing() {
    let aliases = [
        ("config", "properties.config"),
        ("config.Properties.x", "properties.config.Properties.x"),
    ];
    assert_eq!(
        denormalized(&aliases, json!({"config": {"properties": {"x": 1}}})),
        Value::from(json!({"properties": {"config": {"Properties": {"x": 1}}}}))
    );
}

#[test]
fn unclosed_quotes_parse_like_literals() {
    let long = alloc::format!("a{}", "['x]".repeat(path::MAX_SEGMENTS - 1));
    assert_eq!(keys(&long).unwrap().len(), path::MAX_SEGMENTS);
    for (text, expected) in [
        ("a['b]['c']", vec!["a", "b]['c"]),
        ("a['b][\"c\"]", vec!["a", "'b", "c"]),
        ("a[\"b][\"c][d']", vec!["a", "\"b", "\"c", "d'"]),
    ] {
        assert_eq!(keys(text).unwrap(), expected, "{text}");
    }
}

#[test]
fn unparseable_short_name_properties_supplies_casing() {
    let aliases = [
        ("config", "properties.config"),
        (
            "config.Properties.x[5000]",
            "properties.config.Properties.x",
        ),
    ];
    assert_eq!(
        denormalized(&aliases, json!({"config": {"properties": {"x": 1}}})),
        Value::from(json!({"properties": {"config": {"Properties": {"x": 1}}}}))
    );
}

#[test]
fn arm_properties_wrapper_never_supplies_casing() {
    for (arm, versioned) in [
        ("properties.config", "Properties.config"),
        ("properties.config", "PROPERTIES.a..y"),
        ("PROPERTIES.a..y", "properties.config"),
    ] {
        let mut registry = AliasRegistry::new();
        registry
            .load_from_json(
                &json!([{"namespace": "Test", "resourceTypes": [{"resourceType": "widgets", "aliases": [{
                    "name": "Test/widgets/config",
                    "defaultPath": arm,
                    "paths": [{"path": versioned, "apiVersions": ["2024-01-01"]}]
                }]}]}])
                .to_string(),
            )
            .unwrap();
        assert_eq!(
            denormalizer::denormalize_with_aliases(
                &Value::from(json!({"u": {"properties": {"z": 1}}})),
                registry.get("Test/widgets"),
                None
            ),
            Value::from(json!({"properties": {"u": {"properties": {"z": 1}}}})),
            "{arm} {versioned}"
        );
    }
}

fn nest(keys: &[&str], value: Json) -> Json {
    keys.iter()
        .rev()
        .fold(value, |value, key| json!({*key: value}))
}

fn suffix_registry(suffix: &str) -> AliasRegistry {
    let mut registry = AliasRegistry::new();
    registry
        .load_from_json(
            &json!([{
                "namespace": "Test",
                "resourceTypes": [{
                    "resourceType": "widgets",
                    "aliases": [{
                        "name": alloc::format!("Test/widgets/renamed{suffix}"),
                        "defaultPath": alloc::format!("properties.original{suffix}"),
                        "paths": [{
                            "path": alloc::format!("properties.versioned{suffix}"),
                            "apiVersions": ["V2"]
                        }]
                    }]
                }]
            }])
            .to_string(),
        )
        .unwrap();
    registry
}

fn lookup(value: &Value, keys: &[&str]) -> Value {
    let mut current = value;
    for key in keys {
        let Some(next) = current
            .as_object()
            .ok()
            .and_then(|object| object.get(&Value::from(*key)))
        else {
            return Value::Undefined;
        };
        current = next;
    }
    current.clone()
}

#[test]
fn bracket_alias_normalizer_match() {
    let mut failures = Vec::new();
    for (suffix, keys) in cases() {
        let registry = suffix_registry(suffix);
        for (version, source) in [(None, "original"), (Some("v2"), "versioned")] {
            let raw = Value::from_json_str(
                &json!({"type": "Test/widgets", "properties": {source: nest(&keys, json!(42))}})
                    .to_string(),
            )
            .unwrap();
            let normalized = normalizer::normalize(&raw, Some(&registry), version);
            let lowercase: Vec<_> = keys.iter().map(|key| key.to_ascii_lowercase()).collect();
            let mut target = vec!["renamed"];
            target.extend(lowercase.iter().map(|key| key.as_str()));
            let actual = lookup(&normalized, &target);
            if actual != Value::from(42) {
                failures.push(alloc::format!("{suffix} {version:?}: {actual:?}"));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn bracket_alias_normalizer_nonmatch() {
    for (suffix, keys) in cases() {
        let registry = suffix_registry(suffix);
        let raw = Value::from_json_str(
            &json!({"type": "Test/widgets", "properties": {"original": {"different": 42}}})
                .to_string(),
        )
        .unwrap();
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        let lowercase: Vec<_> = keys.iter().map(|key| key.to_ascii_lowercase()).collect();
        let mut target = vec!["renamed"];
        target.extend(lowercase.iter().map(|key| key.as_str()));
        assert_eq!(lookup(&normalized, &target), Value::Undefined, "{suffix}");
    }
    // Raw ARM navigation remains case-sensitive, even for quoted keys.
    let raw =
        Value::from_json_str(r#"{"type":"Test/widgets","properties":{"original":{"aB":42}}}"#)
            .unwrap();
    let normalized = normalizer::normalize(&raw, Some(&suffix_registry("['Ab']")), None);
    assert_eq!(lookup(&normalized, &["renamed", "ab"]), Value::Undefined);
}

#[test]
fn bracket_alias_denormalizer_match() {
    let mut failures = Vec::new();
    for (suffix, keys) in cases() {
        let registry = suffix_registry(suffix);
        for version in [None, Some("v2")] {
            let lowercase: Vec<_> = keys.iter().map(|key| key.to_ascii_lowercase()).collect();
            let refs: Vec<_> = lowercase.iter().map(|key| key.as_str()).collect();
            let normalized = Value::from_json_str(
                &json!({"type": "Test/widgets", "renamed": nest(&refs, json!(42))}).to_string(),
            )
            .unwrap();
            let actual = denormalizer::denormalize(&normalized, Some(&registry), version);
            let source = if version.is_some() {
                "versioned"
            } else {
                "original"
            };
            let mut target = vec!["properties", source];
            target.extend(keys.iter().copied());
            if lookup(&actual, &target) != Value::from(42) {
                failures.push(alloc::format!("{suffix} {version:?}: {actual:?}"));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn bracket_alias_denormalizer_nonmatch() {
    for (suffix, keys) in cases() {
        let registry = suffix_registry(suffix);
        let normalized =
            Value::from_json_str(r#"{"type":"Test/widgets","renamed":{"different":42}}"#).unwrap();
        let actual = denormalizer::denormalize(&normalized, Some(&registry), None);
        let mut target = vec!["properties", "original"];
        target.extend(keys);
        assert_eq!(lookup(&actual, &target), Value::Undefined, "{suffix}");
    }
}

#[test]
fn bracket_alias_denormalizer_preserves_siblings_and_casing() {
    let registry = suffix_registry("['A.B']");
    for (input, expected) in [
        (
            json!({"ReNaMeD": {"A.B": 42, "sibling": 7}}),
            json!({"properties": {"original": {"A.B": 42}, "renamed": {"sibling": 7}}}),
        ),
        (
            json!({"ReNaMeD": {"different": 42, "sibling": 7}}),
            json!({"properties": {"renamed": {"different": 42, "sibling": 7}}}),
        ),
    ] {
        let aliases = registry.get("Test/widgets");
        let actual = denormalizer::denormalize_with_aliases(&Value::from(input), aliases, None);
        assert_eq!(actual, Value::from(expected));
    }
}

#[test]
fn bracket_alias_true_wildcard_with_quoted_leaf() {
    for (suffix, keys) in [
        ("['A.B']", vec!["A.B"]),
        ("['a[*].properties.fake']", vec!["a[*].properties.fake"]),
        ("[outer]['a[b]']", vec!["outer", "a[b]"]),
    ] {
        let mut registry = AliasRegistry::new();
        registry
            .load_from_json(
                &json!([{
                    "namespace": "Test",
                    "resourceTypes": [{
                        "resourceType": "widgets",
                        "aliases": [{
                            "name": alloc::format!("Test/widgets/items[*].renamed{suffix}"),
                            "defaultPath": alloc::format!("properties.items[*].original{suffix}")
                        }]
                    }]
                }])
                .to_string(),
            )
            .unwrap();
        let raw = Value::from(json!({
            "type": "Test/widgets",
            "properties": {"items": [
                {"original": nest(&keys, json!(42))},
                {"original": {"different": 7}}
            ]}
        }));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        let items = lookup(&normalized, &["items"]);
        let items = items.as_array().unwrap();
        let lowercase: Vec<_> = keys.iter().map(|key| key.to_ascii_lowercase()).collect();
        let mut target = vec!["renamed"];
        target.extend(lowercase.iter().map(|key| key.as_str()));
        assert_eq!(
            lookup(items.get(0).unwrap(), &target),
            Value::from(42),
            "{suffix}"
        );
        assert_eq!(
            lookup(items.get(1).unwrap(), &target),
            Value::Undefined,
            "{suffix}"
        );
        let mut source = vec!["original"];
        source.extend(lowercase.iter().map(|key| key.as_str()));
        assert_eq!(
            lookup(items.get(0).unwrap(), &source),
            Value::Undefined,
            "{suffix}"
        );

        let alias_input = Value::from(json!({
            "type": "Test/widgets",
            "items": [
                {"renamed": nest(&lowercase.iter().map(|key| key.as_str()).collect::<Vec<_>>(), json!(42))},
                {"renamed": {"different": 7}}
            ]
        }));
        let arm = registry.denormalize(&alias_input, None);
        let arm_items_value = lookup(&arm, &["properties", "items"]);
        let arm_items = arm_items_value.as_array().unwrap();
        let mut arm_source = vec!["original"];
        arm_source.extend(keys);
        assert_eq!(
            lookup(arm_items.get(0).unwrap(), &arm_source),
            Value::from(42),
            "{suffix}"
        );
        assert_eq!(
            lookup(arm_items.get(1).unwrap(), &arm_source),
            Value::Undefined,
            "{suffix}"
        );
        assert_eq!(
            lookup(arm_items.get(0).unwrap(), &target),
            Value::Undefined,
            "{suffix}"
        );
    }
}

#[test]
fn bracket_alias_array_indices_are_not_quoted_keys() {
    let registry = suffix_registry("[0].leaf");
    for (input_value, expected) in [
        (json!([{"leaf": 42}]), Value::from(42)),
        (json!({"0": {"leaf": 42}}), Value::Undefined),
    ] {
        let input = Value::from(json!({"type": "Test/widgets", "renamed": input_value}));
        let raw =
            Value::from(json!({"type": "Test/widgets", "properties": {"original": input_value}}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        let normalized_value = lookup(&normalized, &["renamed"]);
        let actual = normalized_value
            .as_array()
            .ok()
            .and_then(|array| array.get(0))
            .map_or(Value::Undefined, |value| lookup(value, &["leaf"]));
        assert_eq!(actual, expected);

        let arm = registry.denormalize(&input, None);
        let arm_value = lookup(&arm, &["properties", "original"]);
        let arm_actual = arm_value
            .as_array()
            .ok()
            .and_then(|array| array.get(0))
            .map_or(Value::Undefined, |value| lookup(value, &["leaf"]));
        assert_eq!(arm_actual, expected);
    }
}

#[test]
fn bracket_alias_malformed_paths_do_not_project_whole_resources() {
    for suffix in ["[]", "['']", "[ab", "['ab'].", "[ab]junk"] {
        let registry = suffix_registry(suffix);
        let raw =
            Value::from(json!({"type": "Test/widgets", "properties": {"original": {"ab": 42}}}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert_eq!(
            lookup(&normalized, &["renamed"]),
            Value::Undefined,
            "{suffix}"
        );
        let input = Value::from(json!({"type": "Test/widgets", "renamed": {"ab": 42}}));
        let arm = registry.denormalize(&input, None);
        assert_eq!(
            lookup(&arm, &["properties", "original"]),
            Value::Undefined,
            "{suffix}"
        );
    }
}

#[test]
fn bracket_array_base_renames_round_trip() {
    // The base rename's rendered `['my.arr']` names one key, not two.
    let aliases = [("myArr[*].x", "properties['my.arr'][*].x")];
    assert_eq!(
        normalized(&aliases, json!({"my.arr": [{"x": 1}]})),
        Value::from(json!({"type": "Test/widgets", "myarr": [{"x": 1}]}))
    );
    assert_eq!(
        denormalized(&aliases, json!({"myarr": [{"x": 1}]})),
        Value::from(json!({"properties": {"my.arr": [{"x": 1}]}}))
    );
    // The dotted twin names a nested array, which is renamed as before.
    let dotted = [("myArr[*].x", "properties.my.arr[*].x")];
    assert_eq!(
        normalized(
            &dotted,
            json!({"my.arr": [{"x": 1}], "my": {"arr": [{"x": 2}]}})
        ),
        Value::from(json!({"type": "Test/widgets", "my.arr": [{"x": 1}], "myarr": [{"x": 2}]}))
    );
    assert_eq!(
        denormalized(&dotted, json!({"myarr": [{"x": 2}]})),
        Value::from(json!({"properties": {"my": {"arr": [{"x": 2}]}}}))
    );
}

#[test]
fn indexed_root_properties_write_keeps_short_value() {
    // ARM `properties` is an object, so a scalar alias that indexes it is not
    // written: the value stays at its short path instead of being dropped
    // when the properties object is attached.
    let aliases = [("x", "properties[0].x"), ("z", "properties.z")];
    assert_eq!(
        denormalized(&aliases, json!({"x": 1, "z": 2})),
        Value::from(json!({"properties": {"x": 1, "z": 2}}))
    );
    let keyed = [("x", "properties.y.x"), ("z", "properties.z")];
    assert_eq!(
        denormalized(&keyed, json!({"x": 1, "z": 2})),
        Value::from(json!({"properties": {"y": {"x": 1}, "z": 2}}))
    );
}
