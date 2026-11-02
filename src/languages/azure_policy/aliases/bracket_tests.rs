// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Alias path grammar and parsed alias catalog regressions.

#![allow(clippy::unwrap_used)]

use super::{
    denormalizer, path,
    types::{PrecomputedRemap, PrecomputedReverseRemap, ResolvedEntry, VersionedAggregates},
    AliasRegistry,
};
use crate::Value;
use alloc::string::{String, ToString as _};
use alloc::vec;
use alloc::vec::Vec;
use serde_json::json;

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
    ] {
        assert_eq!(path::parse(text).unwrap().segments, expected, "{text}");
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
fn wildcard_parts_split_only_real_wildcards() {
    assert_eq!(
        path::wildcard_parts("a['[*].b'][*].c[*]"),
        vec!["a['[*].b']", "c", ""]
    );
    assert_eq!(path::wildcard_parts("a..b[*].c"), vec!["a..b[*].c"]);
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
fn quoted_element_leaf_is_remapped() {
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
    assert!(aggregates.array_renames_normalize.is_empty());
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
    let registry = registry(&[
        ("rules[*].x", "properties['rules'][*].x"),
        ("other[*].Leaf", "properties.other[*]['leaf']"),
    ]);
    assert_eq!(
        registry.get("Test/widgets").unwrap().default_aggregates,
        VersionedAggregates::default()
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
}
