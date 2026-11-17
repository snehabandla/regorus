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
    let aggregates = &registry.get("Test/widgets").unwrap().default_aggregates;
    assert!(aggregates.element_remaps.is_empty());
    assert!(aggregates.reverse_element_remaps.is_empty());
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
    let aggregates = &registry.get("Test/widgets").unwrap().default_aggregates;
    assert!(aggregates.element_remaps.is_empty());
    assert!(aggregates.reverse_element_remaps.is_empty());
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
    // An equivalent quoted spelling of the base is not a rename.
    let same = self::registry("Test/widgets", &[("items[*]", "properties['items'][*]")]);
    let aggregates = &same.get("Test/widgets").unwrap().default_aggregates;
    assert!(aggregates.array_renames_normalize.is_empty());
    assert!(aggregates.array_renames_denormalize.is_empty());
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
fn set_pads_indices_and_keeps_dotted_keys() {
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
}

#[test]
fn standalone_properties_leaf_is_not_stripped() {
    assert_eq!(
        path::parse("properties")
            .unwrap()
            .scalar_part()
            .unwrap()
            .without_properties()
            .len(),
        1
    );
    assert_eq!(
        path::parse("properties.a")
            .unwrap()
            .scalar_part()
            .unwrap()
            .without_properties()
            .len(),
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
fn plain_denormalize_consumes_raw_short_path_data() {
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
    // Equivalent up to case: the value stays where Phase 2a put it.
    assert_eq!(
        denorm(&[("a.x", "properties.A.X")], json!({"a": {"x": 1}})),
        Value::from(json!({"properties": {"a": {"x": 1}}}))
    );
}

#[test]
fn reverse_leaf_remaps_precede_base_renames() {
    // Reverse leaf remaps navigate the alias base, so they run before the
    // base is renamed back to its ARM name. (A mixed-case base is not used:
    // the remap's array lookup is case-sensitive.)
    let aliases = [
        ("myrules[*]", "properties.rules[*]"),
        ("myrules[*].x", "properties.rules[*].y"),
    ];
    assert_eq!(
        denorm(&aliases, json!({"myrules": [{"x": 1}]})),
        Value::from(json!({"properties": {"rules": [{"y": 1}]}}))
    );
    let unaliased = [("myrules[*]", "properties.rules[*]")];
    assert_eq!(
        denorm(&unaliased, json!({"myrules": [{"x": 1}]})),
        Value::from(json!({"properties": {"rules": [{"x": 1}]}}))
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

fn round_trip(aliases: &[(&str, &str)], raw: Json, normalized: Option<Json>) {
    let registry = registry("Test/widgets", aliases);
    let raw = Value::from(raw);
    let actual = normalizer::normalize(&raw, Some(&registry), None);
    if let Some(normalized) = normalized {
        assert_eq!(actual, Value::from(normalized), "{aliases:?}");
    }
    assert_eq!(registry.denormalize(&actual, None), raw, "{aliases:?}");
}

#[test]
fn failed_element_remap_keeps_source() {
    assert_eq!(
        denorm(
            &[("rules[*].displayName", "properties.rules[*].target.x")],
            json!({"rules": [{"displayName": "x", "target": 5}, {"displayName": "y"}]})
        ),
        Value::from(json!({"properties": {"rules": [
            {"displayName": "x", "target": 5},
            {"target": {"x": "y"}}
        ]}}))
    );
    round_trip(
        &[("rules[*].display.name", "properties.rules[*].target.x")],
        json!({"type": "Test/widgets", "properties": {"rules": [{"target": {"x": "v"}, "display": 5}]}}),
        Some(json!({"type": "Test/widgets", "rules": [{"target": {"x": "v"}, "display": 5}]})),
    );
}

#[test]
fn element_remap_prunes_emptied_leaf_parents() {
    round_trip(
        &[("items[*].new.x", "properties.items[*].old.y")],
        json!({"type": "Test/widgets", "properties": {"items": [{"old": {"y": 1}}, {"old": {"y": 2, "z": 3}}, {"old": {}}]}}),
        Some(
            json!({"type": "Test/widgets", "items": [{"new": {"x": 1}}, {"new": {"x": 2}, "old": {"z": 3}}, {"old": {}}]}),
        ),
    );
    round_trip(
        &[(
            "items[*].renamed['a.b']",
            "properties.items[*].original['c.d']",
        )],
        json!({"type": "Test/widgets", "properties": {"items": [{"original": {"c.d": 1}}]}}),
        Some(json!({"type": "Test/widgets", "items": [{"renamed": {"a.b": 1}}]})),
    );
}

#[test]
fn whole_properties_alias_round_trips() {
    round_trip(
        &[("x", "properties")],
        json!({"type": "Test/widgets", "properties": {"a": 1}}),
        Some(json!({"type": "Test/widgets", "a": 1, "x": {"a": 1}})),
    );
    assert_eq!(
        denorm(
            &[("x", "properties")],
            json!({"a": 1, "x": {"a": 2, "b": 3}})
        ),
        Value::from(json!({"properties": {"a": 2, "b": 3}}))
    );
    // A non-object value cannot replace `properties`; it stays at its short
    // path.
    assert_eq!(
        denorm(&[("x", "properties")], json!({"x": 5, "a": 1})),
        Value::from(json!({"properties": {"a": 1, "x": 5}}))
    );
}

#[test]
fn root_field_short_path_is_moved() {
    let aliases = [("sku.name", "properties.hardwareProfile.vmSize")];
    assert_eq!(
        denorm(&aliases, json!({"sku": {"name": "D2"}})),
        Value::from(json!({"properties": {"hardwareProfile": {"vmSize": "D2"}}}))
    );
    assert_eq!(
        denorm(&aliases, json!({"sku": {"name": "D2", "tier": "t"}})),
        Value::from(
            json!({"sku": {"tier": "t"}, "properties": {"hardwareProfile": {"vmSize": "D2"}}})
        )
    );
    assert_eq!(
        denorm(&[("sku.name", "sku.name")], json!({"sku": {"name": "D2"}})),
        Value::from(json!({"sku": {"name": "D2"}}))
    );
    round_trip(
        &aliases,
        json!({"type": "Test/widgets", "properties": {"hardwareProfile": {"vmSize": "D2"}}}),
        None,
    );
}

#[test]
fn invalid_short_names_are_skipped_and_dotted_names_parse() {
    for short in ["a..b", "a]", "a."] {
        round_trip(
            &[(short, "properties.x")],
            json!({"type": "Test/widgets", "properties": {"x": 1}}),
            Some(json!({"type": "Test/widgets", "x": 1})),
        );
    }
    round_trip(
        &[("a. b", "properties.x")],
        json!({"type": "Test/widgets", "properties": {"x": 1}}),
        Some(json!({"type": "Test/widgets", "x": 1, "a": {"b": 1}})),
    );
}

#[test]
fn indexed_element_remap_source_is_kept_for_other_aliases() {
    let aliases = [
        ("nics[*].primaryIp", "properties.nics[*].ips[0]"),
        ("nics[*].ips[*]", "properties.nics[*].ips[*]"),
    ];
    round_trip(
        &aliases,
        json!({"type": "Test/widgets", "properties": {"nics": [{"ips": ["a", "b"]}]}}),
        Some(json!({"type": "Test/widgets", "nics": [{"primaryip": "a", "ips": ["a", "b"]}]})),
    );
    let registry = registry("Test/widgets", &aliases);
    assert_eq!(
        registry.denormalize(
            &Value::from(
                json!({"type": "Test/widgets", "nics": [{"primaryip": "z", "ips": ["a", "b"]}]})
            ),
            None,
        ),
        Value::from(json!({"type": "Test/widgets", "properties": {"nics": [{"ips": ["z", "b"]}]}}))
    );
}

#[test]
fn malformed_versioned_path_only_disables_its_version() {
    let mut registry = AliasRegistry::new();
    registry
        .load_from_json(
            &json!([{
                "namespace": "Test",
                "resourceTypes": [{"resourceType": "widgets", "aliases": [{
                    "name": "Test/widgets/flag",
                    "defaultPath": "properties.config.enabled",
                    "paths": [{"path": "properties.future[", "apiVersions": ["v2"]}]
                }]}]
            }])
            .to_string(),
        )
        .unwrap();
    let raw =
        Value::from(json!({"type": "Test/widgets", "properties": {"config": {"enabled": true}}}));
    let normalized = normalizer::normalize(&raw, Some(&registry), None);
    assert_eq!(
        normalized,
        Value::from(json!({"type": "Test/widgets", "config": {"enabled": true}, "flag": true}))
    );
    assert_eq!(registry.denormalize(&normalized, None), raw);
    let versioned = normalizer::normalize(&raw, Some(&registry), Some("v2"));
    assert_eq!(
        versioned,
        Value::from(json!({"type": "Test/widgets", "config": {"enabled": true}}))
    );
}
