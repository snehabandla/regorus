// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Alias path regressions independent of the compiler's field-path parser.

#![allow(clippy::unwrap_used)]

use super::{denormalizer, normalizer, types::ResolvedEntry, AliasRegistry};
use crate::Value;
use alloc::string::ToString as _;
use alloc::vec;
use alloc::vec::Vec;
use serde_json::{json, Value as Json};

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

fn nest(keys: &[&str], value: Json) -> Json {
    keys.iter().rev().fold(value, |value, key| json!({*key: value}))
}

fn registry(suffix: &str) -> AliasRegistry {
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
        let registry = registry(suffix);
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
        let registry = registry(suffix);
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
    let raw = Value::from_json_str(
        r#"{"type":"Test/widgets","properties":{"original":{"aB":42}}}"#,
    )
    .unwrap();
    let normalized = normalizer::normalize(&raw, Some(&registry("['Ab']")), None);
    assert_eq!(lookup(&normalized, &["renamed", "ab"]), Value::Undefined);
}

#[test]
fn bracket_alias_denormalizer_match() {
    let mut failures = Vec::new();
    for (suffix, keys) in cases() {
        let registry = registry(suffix);
        for version in [None, Some("v2")] {
            let lowercase: Vec<_> = keys.iter().map(|key| key.to_ascii_lowercase()).collect();
            let refs: Vec<_> = lowercase.iter().map(|key| key.as_str()).collect();
            let normalized = Value::from_json_str(
                &json!({"type": "Test/widgets", "renamed": nest(&refs, json!(42))}).to_string(),
            )
            .unwrap();
            let actual = denormalizer::denormalize(&normalized, Some(&registry), version);
            let source = if version.is_some() { "versioned" } else { "original" };
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
        let registry = registry(suffix);
        let normalized = Value::from_json_str(
            r#"{"type":"Test/widgets","renamed":{"different":42}}"#,
        )
        .unwrap();
        let actual = denormalizer::denormalize(&normalized, Some(&registry), None);
        let mut target = vec!["properties", "original"];
        target.extend(keys);
        assert_eq!(lookup(&actual, &target), Value::Undefined, "{suffix}");
    }
}

#[test]
fn bracket_alias_wildcard_classification() {
    let mut failures = Vec::new();
    for (short, expected) in [
        ("renamed['a[*]']", false),
        ("renamed['[*].properties.fake']", false),
        ("renamed[\"a[*]b\"]", false),
        ("renamed['a' [*]' ]", false),
        ("renamed[*]", true),
        ("renamed['a[*]'][*].leaf", true),
        ("renamed['a[*]'].*", false),
    ] {
        let entry = ResolvedEntry::new(short.to_string(), "properties.original".to_string(), vec![], None);
        if entry.is_wildcard != expected {
            failures.push(alloc::format!("{short}: expected {expected}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
