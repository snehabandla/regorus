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
