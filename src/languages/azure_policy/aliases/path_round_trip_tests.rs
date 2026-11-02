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
    registry
        .load_from_json(
            &json!([{
                "namespace": namespace,
                "resourceTypes": [{"resourceType": resource, "aliases": entries}]
            }])
            .to_string(),
        )
        .unwrap();
    registry
}

fn denorm(aliases: &[(&str, &str)], input: Json) -> Value {
    let registry = registry("Test/widgets", aliases);
    denormalizer::denormalize_with_aliases(&Value::from(input), registry.get("Test/widgets"), None)
}

#[test]
fn chained_removals_precede_writes() {
    for (input, expected) in [
        (
            json!({"a": 1, "b": 2}),
            json!({"properties": {"b": 1, "c": 2}}),
        ),
        (
            json!({"a": 1, "other": 2}),
            json!({"properties": {"b": 1, "other": 2}}),
        ),
    ] {
        assert_eq!(
            denorm(&[("a", "properties.b"), ("b", "properties.c")], input),
            Value::from(expected)
        );
    }
    assert_eq!(
        denorm(
            &[("a.x", "properties.b.x"), ("b.x", "properties.c.x")],
            json!({"a": {"x": 1}, "b": {"x": 2, "sibling": 3}})
        ),
        Value::from(json!({"properties": {"b": {"x": 1, "sibling": 3}, "c": {"x": 2}}}))
    );
}

#[test]
fn case_insensitive_writes_reuse_containers() {
    for (input, expected) in [
        (
            json!({"Config": {"a": 1, "b": 2}}),
            json!({"properties": {"Config": {"a": 1, "b": 2}}}),
        ),
        (
            json!({"Config": {"a": 1, "other": 2}}),
            json!({"properties": {"Config": {"a": 1, "other": 2}}}),
        ),
    ] {
        assert_eq!(
            denorm(&[("Config.a", "properties.config.a")], input),
            Value::from(expected)
        );
    }
    let mut object = super::obj_map::new_map();
    path::set(
        &mut object,
        &path::scalar_segments("Config.Child").unwrap(),
        Value::from(1),
        false,
    );
    path::set(
        &mut object,
        &path::scalar_segments("config.child").unwrap(),
        Value::from(2),
        false,
    );
    assert_eq!(
        super::obj_map::make_value(object),
        Value::from(json!({"Config": {"Child": 2}}))
    );
}

#[test]
fn equivalent_wildcard_leaves_do_not_self_remap() {
    let registry = registry("Test/widgets", &[("a[*]['name']", "properties.a[*].name")]);
    for value in [json!({"name": "n"}), json!({"other": "n"})] {
        let raw = Value::from(json!({"type": "Test/widgets", "properties": {"a": [value]}}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert_eq!(
            normalized,
            Value::from(json!({"type": "Test/widgets", "a": [value]}))
        );
        assert_eq!(registry.denormalize(&normalized, None), raw);
    }
}

#[test]
fn bracket_properties_root_collision() {
    for short in ["name", "['name']"] {
        let registry = registry("Test/widgets", &[(short, "properties['name']")]);
        for (props, expected) in [
            (
                json!({"name": "property"}),
                json!({"name": "root", "_p_name": "property", "type": "Test/widgets"}),
            ),
            (
                json!({"other": "property"}),
                json!({"name": "root", "other": "property", "type": "Test/widgets"}),
            ),
        ] {
            let raw =
                Value::from(json!({"type": "Test/widgets", "name": "root", "properties": props}));
            let normalized = normalizer::normalize(&raw, Some(&registry), None);
            assert_eq!(normalized, Value::from(expected));
            assert_eq!(registry.denormalize(&normalized, None), raw);
        }
    }
}

#[test]
fn empty_wildcard_leaf_does_not_delete_value() {
    let registry = registry("Test/widgets", &[("a[*]", "properties.a[*].value")]);
    for value in [json!({"value": 1}), json!({"other": 1})] {
        let raw = Value::from(json!({"type": "Test/widgets", "properties": {"a": [value]}}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert_eq!(
            normalized,
            Value::from(json!({"type": "Test/widgets", "a": [value]}))
        );
        assert_eq!(registry.denormalize(&normalized, None), raw);
    }
}

#[test]
fn unsuccessful_writes_preserve_short_value() {
    for arm in [
        "properties",
        "properties.target.x",
        "properties[",
        "properties[]",
    ] {
        assert_eq!(
            denorm(
                &[("alias.x", arm)],
                json!({"alias": {"x": 1, "sibling": 3}, "target": 7})
            ),
            Value::from(json!({"properties": {"alias": {"x": 1, "sibling": 3}, "target": 7}})),
            "{arm}"
        );
    }
    assert_eq!(
        denorm(
            &[("alias.x", "properties.target.x")],
            json!({"alias": {"x": 1}, "target": {}})
        ),
        Value::from(json!({"properties": {"target": {"x": 1}}}))
    );
    assert_eq!(
        denorm(&[("a", "properties.a.x")], json!({"a": 1})),
        Value::from(json!({"properties": {"a": {"x": 1}}}))
    );
    assert_eq!(
        denorm(
            &[("a", "properties.target"), ("b.x", "properties.target.x")],
            json!({"a": 1, "b": {"x": 2, "sibling": 3}})
        ),
        Value::from(json!({"properties": {"target": 1, "b": {"x": 2, "sibling": 3}}}))
    );
}

#[test]
fn consumed_array_index_is_pruned() {
    for (input, expected) in [
        (
            json!({"rules": [1]}),
            json!({"properties": {"firstRule": 1}}),
        ),
        (json!({"rules": []}), json!({"properties": {"rules": []}})),
        (
            json!({"rules": [1, 2]}),
            json!({"properties": {"firstRule": 1, "rules": [null, 2]}}),
        ),
    ] {
        assert_eq!(
            denorm(&[("rules[0]", "properties.firstRule")], input),
            Value::from(expected)
        );
    }
}

#[test]
fn non_key_array_chain_still_renames_base() {
    for (short, renamed) in [
        ("a[*][*].b", json!({"a": [{"z": 1}]})),
        ("a[0].b[*].c", json!({"a": [{"b": [{"z": 1}]}]})),
    ] {
        let registry = registry("Test/widgets", &[(short, "properties.x[*].z")]);
        let aliases = registry.get("Test/widgets").unwrap();
        assert!(
            !aliases
                .default_aggregates
                .array_renames_normalize
                .is_empty(),
            "{short}"
        );
        let raw = Value::from(json!({"type": "Test/widgets", "properties": {"x": [{"z": 1}]}}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        let mut expected = renamed;
        expected
            .as_object_mut()
            .unwrap()
            .insert("type".into(), json!("Test/widgets"));
        assert_eq!(normalized, Value::from(expected), "{short}");
        let unrelated =
            Value::from(json!({"type": "Test/widgets", "properties": {"other": [{"z": 1}]}}));
        assert_eq!(
            normalizer::normalize(&unrelated, Some(&registry), None),
            Value::from(json!({"type": "Test/widgets", "other": [{"z": 1}]})),
            "{short}"
        );
    }
}

#[test]
fn data_plane_removes_from_phase_2a_destination() {
    let registry = registry("Test.Data/widgets", &[("a.b", "x.b")]);
    for (input, expected) in [
        (
            json!({"type": "Test.Data/widgets", "a": {"b": 1, "sibling": 2}}),
            json!({"type": "Test.Data/widgets", "a": {"sibling": 2}, "x": {"b": 1}}),
        ),
        (
            json!({"type": "Test.Data/widgets", "a": {"other": 1, "sibling": 2}}),
            json!({"type": "Test.Data/widgets", "a": {"other": 1, "sibling": 2}}),
        ),
    ] {
        assert_eq!(
            registry.denormalize(&Value::from(input), None),
            Value::from(expected)
        );
    }
}

#[test]
fn bracket_properties_array_base() {
    let registry = registry("Test/widgets", &[("renamed[*]", "properties['items'][*]")]);
    for items in [json!([{"name": "n"}]), json!([])] {
        let raw = Value::from(json!({"type": "Test/widgets", "properties": {"items": items}}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert_eq!(
            normalized,
            Value::from(json!({"type": "Test/widgets", "renamed": items}))
        );
        assert_eq!(registry.denormalize(&normalized, None), raw);
    }
    let unrelated = Value::from(json!({"type": "Test/widgets", "properties": {"other": []}}));
    let normalized_unrelated = normalizer::normalize(&unrelated, Some(&registry), None);
    assert_eq!(
        normalized_unrelated,
        Value::from(json!({"type": "Test/widgets", "other": []}))
    );
    assert_eq!(registry.denormalize(&normalized_unrelated, None), unrelated);
}

#[test]
fn index_padding_is_bounded() {
    assert!(path::scalar_segments("a[1000000000]").is_none());
    assert!(path::scalar_segments("a[99999999999999999999999999999]").is_none());
    assert!(path::scalar_segments("a[2]").is_some());
    let segments = vec![
        path::Segment::Key(crate::Rc::from("a")),
        path::Segment::Index(1000000000),
    ];
    let mut map = super::obj_map::new_map();
    path::set(&mut map, &segments, Value::from(1), false);
    assert_eq!(super::obj_map::make_value(map), Value::from(json!({})));
}

#[test]
fn round_trips() {
    for (resource_type, aliases, raw_json, normalized_json) in [
        (
            "Test/widgets",
            vec![("renamed['Mixed.Key']", "properties.original['Mixed.Key']")],
            json!({"type": "Test/widgets", "properties": {"original": {"Mixed.Key": 1, "sibling": 2}}}),
            json!({"original": {"mixed.key": 1, "sibling": 2}, "renamed": {"mixed.key": 1}, "type": "Test/widgets"}),
        ),
        (
            "Test/widgets",
            vec![("renamed[2].leaf", "properties.original[2].leaf")],
            json!({"type": "Test/widgets", "properties": {"original": [null, null, {"leaf": 1, "sibling": 2}]}}),
            json!({"original": [null, null, {"leaf": 1, "sibling": 2}], "renamed": [null, null, {"leaf": 1}], "type": "Test/widgets"}),
        ),
        (
            "Test/widgets",
            vec![("renamed['a.b']", "properties.original['a.b']")],
            json!({"type": "Test/widgets", "properties": {"original": {"a.b": 1, "sibling": 2}}}),
            json!({"original": {"a.b": 1, "sibling": 2}, "renamed": {"a.b": 1}, "type": "Test/widgets"}),
        ),
        (
            "Test/widgets",
            vec![("renamed[0].leaf", "properties.original[0].leaf")],
            json!({"type": "Test/widgets", "properties": {"original": [{"leaf": 1, "sibling": 2}]}}),
            json!({"original": [{"leaf": 1, "sibling": 2}], "renamed": [{"leaf": 1}], "type": "Test/widgets"}),
        ),
        (
            "Test/widgets",
            vec![("Config.a", "properties.config.a")],
            json!({"type": "Test/widgets", "properties": {"Config": {"a": 1, "b": 2}}}),
            json!({"config": {"a": 1, "b": 2}, "type": "Test/widgets"}),
        ),
        (
            "Test/widgets",
            vec![("a", "properties.b"), ("b", "properties.c")],
            json!({"type": "Test/widgets", "properties": {"b": 1, "c": 2}}),
            json!({"a": 1, "b": 2, "c": 2, "type": "Test/widgets"}),
        ),
        (
            "Test.Data/widgets",
            vec![("a.b", "x.b")],
            json!({"type": "Test.Data/widgets", "x": {"b": 1, "sibling": 2}}),
            json!({"a": {"b": 1}, "type": "Test.Data/widgets", "x": {"b": 1, "sibling": 2}}),
        ),
    ] {
        let registry = registry(resource_type, &aliases);
        let raw = Value::from(raw_json);
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert_eq!(
            normalized,
            Value::from(normalized_json),
            "{resource_type}: {aliases:?}"
        );
        assert_eq!(
            registry.denormalize(&normalized, None),
            raw,
            "{resource_type}: {aliases:?}"
        );
    }
}

#[test]
fn parser_and_padding_discriminators() {
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
    for text in ["a..b", "a[]", "a['']", "a[", "a[b]junk", "a."] {
        assert!(path::parse(text).is_none(), "{text}");
    }
    let mut map = super::obj_map::new_map();
    path::set(
        &mut map,
        &path::scalar_segments("a[2]['Key.With.Dot']").unwrap(),
        Value::from(7),
        false,
    );
    assert_eq!(
        super::obj_map::make_value(map),
        Value::from(json!({"a": [null, null, {"Key.With.Dot": 7}]}))
    );
    let entries = registry(
        "Test/widgets",
        &[("a['Mixed.Key']", "properties.a['Mixed.Key']")],
    );
    let restored = denormalizer::denormalize_with_aliases(
        &Value::from(json!({"unaliased": {"mixed.key": 7}})),
        entries.get("Test/widgets"),
        None,
    );
    assert_eq!(
        restored,
        Value::from(json!({"properties": {"unaliased": {"Mixed.Key": 7}}}))
    );
}

fn round_trip_with_provenance(
    aliases: &[(&str, &str)],
    raw: Json,
    normalized: Json,
) -> (AliasRegistry, super::types::AliasProvenance) {
    let registry = registry("Test/widgets", aliases);
    let raw = Value::from(raw);
    let (actual, provenance) = registry.normalize_with_provenance(&raw, None);
    assert_eq!(actual, Value::from(normalized), "{aliases:?}");
    assert_eq!(
        registry.denormalize_with_provenance(&actual, None, &provenance),
        raw,
        "{aliases:?}"
    );
    (registry, provenance)
}

#[test]
fn standalone_properties_leaf_is_not_stripped() {
    assert_eq!(
        path::without_properties(&path::scalar_segments("properties").unwrap()).len(),
        1
    );
    assert_eq!(
        path::without_properties(&path::scalar_segments("properties.a").unwrap()).len(),
        1
    );
    let registry = registry(
        "Test/widgets",
        &[("items[*].config", "properties.items[*].properties")],
    );
    let raw = Value::from(json!({
        "type": "Test/widgets",
        "properties": {"items": [{"properties": {"a": 1}, "name": "n"}]}
    }));
    let normalized = normalizer::normalize(&raw, Some(&registry), None);
    assert_eq!(
        normalized,
        Value::from(json!({"type": "Test/widgets", "items": [{"config": {"a": 1}, "name": "n"}]}))
    );
    assert_eq!(registry.denormalize(&normalized, None), raw);
}

#[test]
fn reverse_element_remap_cleanup_is_case_insensitive() {
    for field in ["displayName", "DisplayName", "displayname"] {
        let mut element = serde_json::Map::new();
        element.insert(field.into(), json!("x"));
        assert_eq!(
            denorm(
                &[("rules[*].displayName", "properties.rules[*].name")],
                json!({"rules": [element]})
            ),
            Value::from(json!({"properties": {"rules": [{"name": "x"}]}})),
            "{field}"
        );
    }
}

#[test]
fn provenance_preserves_raw_short_path_data() {
    round_trip_with_provenance(
        &[("settings.flag", "properties.flag")],
        json!({"type": "Test/widgets", "properties": {"settings": {"flag": true, "other": 1}}}),
        json!({"type": "Test/widgets", "settings": {"flag": true, "other": 1}}),
    );
    round_trip_with_provenance(
        &[("rules[0]", "properties.firstRule")],
        json!({"type": "Test/widgets", "properties": {"rules": [5, 6]}}),
        json!({"type": "Test/widgets", "rules": [5, 6]}),
    );
    round_trip_with_provenance(
        &[("flag", "properties.other")],
        json!({"type": "Test/widgets", "properties": {"flag": 1}}),
        json!({"type": "Test/widgets", "flag": 1}),
    );
    // Without a record, plain denormalize consumes every alias value.
    let registry = registry("Test/widgets", &[("settings.flag", "properties.flag")]);
    assert_eq!(
        registry.denormalize(
            &Value::from(json!({"type": "Test/widgets", "settings": {"flag": true, "other": 1}})),
            None
        ),
        Value::from(
            json!({"type": "Test/widgets", "properties": {"flag": true, "settings": {"other": 1}}})
        )
    );
}

#[test]
fn provenance_maps_values_added_after_normalization() {
    let (registry, provenance) = round_trip_with_provenance(
        &[
            ("settings.flag", "properties.flag"),
            ("rules[1]", "properties.second"),
        ],
        json!({"type": "Test/widgets", "properties": {"other": 1}}),
        json!({"type": "Test/widgets", "other": 1}),
    );
    let modified = Value::from(json!({
        "type": "Test/widgets", "other": 1, "settings": {"flag": true}, "rules": [null, 2]
    }));
    assert_eq!(
        registry.denormalize_with_provenance(&modified, None, &provenance),
        Value::from(json!({
            "type": "Test/widgets",
            "properties": {"other": 1, "flag": true, "second": 2}
        }))
    );
}

#[test]
fn provenance_prunes_only_padding_and_consumed_nulls() {
    round_trip_with_provenance(
        &[("rules[1]", "properties.second")],
        json!({"type": "Test/widgets", "properties": {"second": 6}}),
        json!({"type": "Test/widgets", "rules": [null, 6], "second": 6}),
    );
    round_trip_with_provenance(
        &[("rules[1]", "properties.second")],
        json!({"type": "Test/widgets", "properties": {"rules": [null], "second": 6}}),
        json!({"type": "Test/widgets", "rules": [null, 6], "second": 6}),
    );
    round_trip_with_provenance(
        &[("rules[0]", "properties.first")],
        json!({"type": "Test/widgets", "properties": {"rules": [], "first": 6}}),
        json!({"type": "Test/widgets", "rules": [6], "first": 6}),
    );
    round_trip_with_provenance(
        &[
            ("rules[0]", "properties.first"),
            ("rules[1]", "properties.second"),
        ],
        json!({"type": "Test/widgets", "properties": {"first": 5, "second": 6}}),
        json!({"type": "Test/widgets", "rules": [5, 6], "first": 5, "second": 6}),
    );
    round_trip_with_provenance(
        &[("a.b", "properties.c")],
        json!({"type": "Test/widgets", "properties": {"a": {}, "c": 1}}),
        json!({"type": "Test/widgets", "a": {"b": 1}, "c": 1}),
    );
    round_trip_with_provenance(
        &[("x[1]", "properties.y")],
        json!({"type": "Test/widgets", "properties": {"x": [null, null, 3], "y": 5}}),
        json!({"type": "Test/widgets", "x": [null, 5, 3], "y": 5}),
    );
}

#[test]
fn failed_single_key_write_keeps_source() {
    assert_eq!(
        denorm(&[("a", "properties.t.x")], json!({"a": 1, "t": 5})),
        Value::from(json!({"properties": {"a": 1, "t": 5}}))
    );
}

#[test]
fn equivalent_path_without_sibling_is_kept() {
    assert_eq!(
        denorm(&[("a.x", "properties.a.x")], json!({"a": {"x": 1}})),
        Value::from(json!({"properties": {"a": {"x": 1}}}))
    );
}

#[test]
fn base_rename_and_leaf_remap_denormalize() {
    assert_eq!(
        denorm(
            &[("renamed[*].leaf", "properties.original[*].arm")],
            json!({"renamed": [{"leaf": 1, "other": 2}]})
        ),
        Value::from(json!({"properties": {"original": [{"arm": 1, "other": 2}]}}))
    );
}

#[test]
fn set_replaces_null_with_containers() {
    for (input, path_text, expected) in [
        (json!({"a": null}), "a.b", json!({"a": {"b": 1}})),
        (json!({"a": null}), "a[1]", json!({"a": [null, 1]})),
        (json!({"a": [null]}), "a[0].b", json!({"a": [{"b": 1}]})),
        (json!({"a": [null]}), "a[0][1]", json!({"a": [[null, 1]]})),
        (json!({"a": 3}), "a.b", json!({"a": 3})),
    ] {
        let mut map = super::obj_map::new_map();
        for (key, value) in input.as_object().unwrap() {
            map.insert(crate::Rc::from(key.as_str()), Value::from(value.clone()));
        }
        path::set(
            &mut map,
            &path::scalar_segments(path_text).unwrap(),
            Value::from(1),
            false,
        );
        assert_eq!(
            super::obj_map::make_value(map),
            Value::from(expected),
            "{path_text}"
        );
    }
}

#[test]
fn rename_guards() {
    for (input, source, target, expected) in [
        (json!({"a": 1, "b": 2}), "a", "b", json!({"a": 1, "b": 2})),
        (json!({"a": 1}), "a", "A", json!({"a": 1})),
        (json!({"a": 1, "b": 2}), "a", "b.c", json!({"a": 1, "b": 2})),
        (json!({"b": 2}), "a", "c", json!({"b": 2})),
        (json!({"a": 1}), "a[*]", "c", json!({"a": 1})),
        (json!({"a": {"x": 1}}), "a.x", "b[0]", json!({"b": [1]})),
    ] {
        let mut map = super::obj_map::new_map();
        for (key, value) in input.as_object().unwrap() {
            map.insert(crate::Rc::from(key.as_str()), Value::from(value.clone()));
        }
        path::rename(&mut map, source, target, false);
        assert_eq!(
            super::obj_map::make_value(map),
            Value::from(expected),
            "{source} -> {target}"
        );
    }
}

#[test]
fn index_bound_is_inclusive_at_max() {
    assert!(path::scalar_segments("a[4095]").is_some());
    assert!(path::scalar_segments("a[4096]").is_none());
    let mut map = super::obj_map::new_map();
    path::set(
        &mut map,
        &path::scalar_segments("a[4095]").unwrap(),
        Value::from(1),
        false,
    );
    let value = super::obj_map::make_value(map);
    let array = value
        .as_object()
        .unwrap()
        .get(&Value::from("a"))
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(array.len(), 4096);
}
