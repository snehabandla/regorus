// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::unwrap_used)]

use super::{denormalizer, normalizer, path, AliasRegistry};
use crate::Value;
use alloc::string::ToString as _;
use alloc::vec;
use serde_json::{json, Value as Json};

fn registry(resource_type: &str, aliases: &[(&str, &str)]) -> AliasRegistry {
    let entries: alloc::vec::Vec<_> = aliases.iter().map(|(short, arm)| {
        json!({"name": alloc::format!("{resource_type}/{short}"), "defaultPath": arm})
    }).collect();
    let mut registry = AliasRegistry::new();
    let (namespace, resource) = resource_type.split_once('/').unwrap();
    registry.load_from_json(&json!([{
        "namespace": namespace,
        "resourceTypes": [{"resourceType": resource, "aliases": entries}]
    }]).to_string()).unwrap();
    registry
}

fn denorm(aliases: &[(&str, &str)], input: Json) -> Value {
    let registry = registry("Test/widgets", aliases);
    denormalizer::denormalize_with_aliases(&Value::from(input), registry.get("Test/widgets"), None)
}

#[test]
fn review_chained_removals_precede_writes_r1_1() {
    for (input, expected) in [
        (json!({"a": 1, "b": 2}), json!({"properties": {"b": 1, "c": 2}})),
        (json!({"a": 1, "other": 2}), json!({"properties": {"b": 1, "other": 2}})),
    ] {
        assert_eq!(denorm(&[("a", "properties.b"), ("b", "properties.c")], input), Value::from(expected));
    }
    assert_eq!(
        denorm(&[("a.x", "properties.b.x"), ("b.x", "properties.c.x")], json!({"a": {"x": 1}, "b": {"x": 2, "sibling": 3}})),
        Value::from(json!({"properties": {"b": {"x": 1, "sibling": 3}, "c": {"x": 2}}}))
    );
}

#[test]
fn review_case_insensitive_writes_reuse_containers_r1_2() {
    for (input, expected) in [
        (json!({"Config": {"a": 1, "b": 2}}), json!({"properties": {"Config": {"a": 1, "b": 2}}})),
        (json!({"Config": {"a": 1, "other": 2}}), json!({"properties": {"Config": {"a": 1, "other": 2}}})),
    ] {
        assert_eq!(denorm(&[("Config.a", "properties.config.a")], input), Value::from(expected));
    }
    let mut object = super::obj_map::new_map();
    path::set(&mut object, &path::scalar_segments("Config.Child").unwrap(), Value::from(1), false);
    path::set(&mut object, &path::scalar_segments("config.child").unwrap(), Value::from(2), false);
    assert_eq!(super::obj_map::make_value(object), Value::from(json!({"Config": {"Child": 2}})));
}

#[test]
fn review_equivalent_wildcard_leaves_do_not_self_remap_r1_3() {
    let registry = registry("Test/widgets", &[("a[*]['name']", "properties.a[*].name")]);
    for value in [json!({"name": "n"}), json!({"other": "n"})] {
        let raw = Value::from(json!({"type": "Test/widgets", "properties": {"a": [value]}}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert_eq!(normalized, Value::from(json!({"type": "Test/widgets", "a": [value]})));
        assert_eq!(registry.denormalize(&normalized, None), raw);
    }
}

#[test]
fn review_bracket_properties_root_collision_r1_4() {
    let registry = registry("Test/widgets", &[("name", "properties['name']")]);
    for (props, expected) in [
        (json!({"name": "property"}), json!({"name": "root", "_p_name": "property", "type": "Test/widgets"})),
        (json!({"other": "property"}), json!({"name": "root", "other": "property", "type": "Test/widgets"})),
    ] {
        let raw = Value::from(json!({"type": "Test/widgets", "name": "root", "properties": props}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert_eq!(normalized, Value::from(expected));
        assert_eq!(registry.denormalize(&normalized, None), raw);
    }
}

#[test]
fn review_empty_wildcard_leaf_does_not_delete_value_r1_5() {
    let registry = registry("Test/widgets", &[("a[*]", "properties.a[*].value")]);
    for value in [json!({"value": 1}), json!({"other": 1})] {
        let raw = Value::from(json!({"type": "Test/widgets", "properties": {"a": [value]}}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert_eq!(normalized, Value::from(json!({"type": "Test/widgets", "a": [value]})));
        assert_eq!(registry.denormalize(&normalized, None), raw);
    }
}

#[test]
fn review_unsuccessful_writes_preserve_short_value_r1_6() {
    for arm in ["properties", "properties.target.x", "properties[", "properties[]"] {
        assert_eq!(
            denorm(&[("alias.x", arm)], json!({"alias": {"x": 1, "sibling": 3}, "target": 7})),
            Value::from(json!({"properties": {"alias": {"x": 1, "sibling": 3}, "target": 7}})),
            "{arm}"
        );
    }
    assert_eq!(denorm(&[("alias.x", "properties.target.x")], json!({"alias": {"x": 1}, "target": {}})),
        Value::from(json!({"properties": {"target": {"x": 1}}})));
}

#[test]
fn review_consumed_array_index_is_pruned_r1_7() {
    for (input, expected) in [
        (json!({"rules": [1]}), json!({"properties": {"firstRule": 1}})),
        (json!({"rules": []}), json!({"properties": {"rules": []}})),
        (json!({"rules": [1, 2]}), json!({"properties": {"firstRule": 1, "rules": [null, 2]}})),
    ] {
        assert_eq!(denorm(&[("rules[0]", "properties.firstRule")], input), Value::from(expected));
    }
}

#[test]
fn review_non_key_array_chain_still_renames_base_r1_8() {
    for short in ["a[*][*].b", "a[0].b[*].c"] {
        let registry = registry("Test/widgets", &[(short, "properties.x[*].z")]);
        let aliases = registry.get("Test/widgets").unwrap();
        assert!(!aliases.default_aggregates.array_renames_normalize.is_empty(), "{short}");
        let raw = Value::from(json!({"type": "Test/widgets", "properties": {"x": [{"z": 1}]}}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert!(!normalized.as_object().unwrap().contains_key(&Value::from("x")), "{short}");
    }
}

#[test]
fn review_data_plane_removes_from_phase_2a_destination_r1_9() {
    let registry = registry("Test.Data/widgets", &[("a.b", "x.b")]);
    for (input, expected) in [
        (json!({"type": "Test.Data/widgets", "a": {"b": 1, "sibling": 2}}),
         json!({"type": "Test.Data/widgets", "a": {"sibling": 2}, "x": {"b": 1}})),
        (json!({"type": "Test.Data/widgets", "a": {"other": 1, "sibling": 2}}),
         json!({"type": "Test.Data/widgets", "a": {"other": 1, "sibling": 2}})),
    ] {
        assert_eq!(registry.denormalize(&Value::from(input), None), Value::from(expected));
    }
}

#[test]
fn review_bracket_properties_array_base_r1_10() {
    let registry = registry("Test/widgets", &[("renamed[*]", "properties['items'][*]")]);
    for items in [json!([{"name": "n"}]), json!([])] {
        let raw = Value::from(json!({"type": "Test/widgets", "properties": {"items": items}}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert_eq!(normalized, Value::from(json!({"type": "Test/widgets", "renamed": items})));
        assert_eq!(registry.denormalize(&normalized, None), raw);
    }
}

#[test]
fn review_index_padding_is_bounded_r1_12() {
    assert!(path::scalar_segments("a[1000000000]").is_none());
    assert!(path::scalar_segments("a[99999999999999999999999999999]").is_none());
    assert!(path::scalar_segments("a[2]").is_some());
}

#[test]
fn review_round_trips_r1_t() {
    for (resource_type, aliases, raw_json) in [
        ("Test/widgets", vec![("renamed['a.b']", "properties.original['a.b']")],
         json!({"type": "Test/widgets", "properties": {"original": {"a.b": 1, "sibling": 2}}})),
        ("Test/widgets", vec![("renamed[0].leaf", "properties.original[0].leaf")],
         json!({"type": "Test/widgets", "properties": {"original": [{"leaf": 1, "sibling": 2}]}})),
        ("Test/widgets", vec![("Config.a", "properties.config.a")],
         json!({"type": "Test/widgets", "properties": {"config": {"a": 1, "b": 2}}})),
        ("Test/widgets", vec![("a", "properties.b"), ("b", "properties.c")],
         json!({"type": "Test/widgets", "properties": {"b": 1, "c": 2}})),
        ("Test.Data/widgets", vec![("a.b", "x.b")],
         json!({"type": "Test.Data/widgets", "x": {"b": 1, "sibling": 2}})),
    ] {
        let registry = registry(resource_type, &aliases);
        let raw = Value::from(raw_json);
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert_eq!(registry.denormalize(&normalized, None), raw, "{resource_type}: {aliases:?}");
    }
}

#[test]
fn review_parser_and_padding_discriminators_r1_t() {
    for (text, wildcard) in [("a[*]", true), ("a[ * ]", false), ("a['*']", false), ("a['[*]']", false)] {
        let parsed = path::parse(text).unwrap();
        assert_eq!(parsed.segments.contains(&path::Segment::Wildcard), wildcard, "{text}");
    }
    for text in ["a..b", "a[]", "a['']", "a[", "a[b]junk", "a."] {
        assert!(path::parse(text).is_none(), "{text}");
    }
    let mut map = super::obj_map::new_map();
    path::set(&mut map, &path::scalar_segments("a[2]['Key.With.Dot']").unwrap(), Value::from(7), false);
    assert_eq!(super::obj_map::make_value(map), Value::from(json!({"a": [null, null, {"Key.With.Dot": 7}]})));
    let entries = registry("Test/widgets", &[("a['Mixed.Key']", "properties.a['Mixed.Key']")]);
    let restored = denormalizer::denormalize_with_aliases(
        &Value::from(json!({"unaliased": {"mixed.key": 7}})),
        entries.get("Test/widgets"),
        None,
    );
    assert_eq!(restored, Value::from(json!({"properties": {"unaliased": {"Mixed.Key": 7}}})));
}
