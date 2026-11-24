// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::unwrap_used)]

use super::obj_map::{make_value, new_map, ObjMap};
use super::path::{self, Segment};
use super::{denormalizer, normalizer, AliasRegistry};
use crate::Value;
use alloc::string::ToString as _;
use alloc::vec;
use serde_json::{json, Value as Json};

fn map_of(input: Json) -> ObjMap {
    let mut map = new_map();
    for (key, value) in input.as_object().unwrap() {
        map.insert(crate::Rc::from(key.as_str()), Value::from(value.clone()));
    }
    map
}

fn segments(path_text: &str) -> vec::Vec<Segment> {
    path::scalar_segments(path_text).unwrap()
}

#[test]
fn case_insensitive_set_reuses_keys() {
    let mut map = new_map();
    path::set(&mut map, &segments("Config.Child"), Value::from(1), false);
    path::set(&mut map, &segments("config.child"), Value::from(2), false);
    assert_eq!(
        make_value(map),
        Value::from(json!({"Config": {"Child": 2}}))
    );
    let mut lowered = new_map();
    path::set(
        &mut lowered,
        &segments("Config.Child"),
        Value::from(1),
        true,
    );
    assert_eq!(
        make_value(lowered),
        Value::from(json!({"config": {"child": 1}}))
    );
}

#[test]
fn get_follows_parsed_segments() {
    let value = Value::from(json!({"A": {"b.c": [10, {"D": 2}]}}));
    let get = |path_text: &str, case_insensitive| {
        path::get(&value, &segments(path_text), case_insensitive).cloned()
    };
    assert_eq!(get("A['b.c'][0]", false), Some(Value::from(10)));
    assert_eq!(get("a['b.c'][1].d", true), Some(Value::from(2)));
    assert_eq!(get("a['b.c'][1].d", false), None);
    assert_eq!(get("A.b.c", false), None);
    assert_eq!(get("A['b.c'][2]", false), None);
    let wildcard = path::parse("A['b.c'][*]").unwrap();
    assert!(wildcard.scalar_part().is_none());
    let scalar = path::parse("A['b.c'][0]").unwrap();
    assert_eq!(
        scalar.scalar_part().unwrap().segments,
        &segments("A['b.c'][0]")[..]
    );
    assert!(path::get(&value, &wildcard.segments, false).is_none());
    assert!(path::scalar_segments("A[*]").is_none());
}

#[test]
fn remove_prunes_only_emptied_containers() {
    for (input, path_text, expected) in [
        (json!({"a": {"b": 1}}), "a.b", json!({})),
        (
            json!({"a": {"b": 1, "c": 2}}),
            "A.B",
            json!({"a": {"c": 2}}),
        ),
        (json!({"a": [1]}), "a[0]", json!({})),
        (json!({"a": [1, 2]}), "a[0]", json!({"a": [null, 2]})),
        (json!({"a": [{"b": 1}]}), "a[0].b", json!({})),
        (json!({"a": 3}), "a.b", json!({"a": 3})),
        (json!({"a": {"b": 1}}), "a.x", json!({"a": {"b": 1}})),
        (json!({"a": {}}), "a.x", json!({"a": {}})),
        (json!({"a": [null]}), "a[0]", json!({"a": [null]})),
        (json!({"Ab": 1, "ab": 2}), "ab", json!({"Ab": 1})),
        (json!({"a": [{}]}), "a[0].x", json!({"a": [{}]})),
    ] {
        let mut map = map_of(input);
        path::remove(&mut map, &segments(path_text));
        assert_eq!(make_value(map), Value::from(expected), "{path_text}");
    }
    for (prune, expected) in [(true, json!({})), (false, json!({"a": {}}))] {
        let mut object = Value::from(json!({"a": {"b": 1}}));
        let emptied = path::remove_object(object.as_object_mut().unwrap(), &segments("a.b"), prune);
        assert_eq!(emptied, prune);
        assert_eq!(object, Value::from(expected));
    }
}

#[test]
fn can_set_requires_compatible_shapes() {
    let map = map_of(json!({"a": {"b": 1}, "n": null, "arr": [1]}));
    for (path_text, expected) in [
        ("x.y", true),
        ("A.c", true),
        ("a.b", true),
        ("a.b.c", false),
        ("n.x[0]", true),
        ("arr[3]", true),
        ("x[4095]", true),
        ("arr.x", false),
        ("a[0]", false),
        ("arr[0].x", false),
    ] {
        assert_eq!(
            path::can_set(&map, &segments(path_text)),
            expected,
            "{path_text}"
        );
    }
    let too_far = [
        Segment::Key(crate::Rc::from("x")),
        Segment::Index(path::MAX_INDEX + 1),
    ];
    assert!(!path::can_set(&map, &too_far));
    let wildcard = path::parse("x[*]").unwrap();
    assert!(!path::can_set(&map, &wildcard.segments));
    let object = Value::from(json!({"A": 1}));
    let object = object.as_object().unwrap();
    assert!(path::can_set_object(object, &segments("b.c")));
    assert!(!path::can_set_object(object, &segments("a.c")));
}

#[test]
fn set_object_writes_inside_element_objects() {
    let mut object = Value::from(json!({"Tags": {"x": 1}}));
    let inner = object.as_object_mut().unwrap();
    path::set_object(inner, &segments("tags.y"), Value::from(2), true);
    path::set_object(inner, &segments("New[1]"), Value::from(3), true);
    assert_eq!(
        object,
        Value::from(json!({"Tags": {"x": 1, "y": 2}, "new": [null, 3]}))
    );
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
    let mut map = new_map();
    path::set(&mut map, &segments, Value::from(1), false);
    assert_eq!(make_value(map), Value::from(json!({})));
}

#[test]
fn set_pads_indices_and_keeps_dotted_keys() {
    let mut map = new_map();
    path::set(
        &mut map,
        &path::scalar_segments("a[2]['Key.With.Dot']").unwrap(),
        Value::from(7),
        false,
    );
    assert_eq!(
        make_value(map),
        Value::from(json!({"a": [null, null, {"Key.With.Dot": 7}]}))
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
        let mut map = new_map();
        for (key, value) in input.as_object().unwrap() {
            map.insert(crate::Rc::from(key.as_str()), Value::from(value.clone()));
        }
        path::set(
            &mut map,
            &path::scalar_segments(path_text).unwrap(),
            Value::from(1),
            false,
        );
        assert_eq!(make_value(map), Value::from(expected), "{path_text}");
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
        // Pruning `Ab` would make `ab` resolve to `aB`.
        (
            json!({"Ab": {"x": 1}, "aB": 0}),
            "Ab.x",
            "ab.y",
            json!({"Ab": {"x": 1}, "aB": 0}),
        ),
        (
            json!({"Ab": {"x": 1}, "aB": {"y": 2}}),
            "Ab.x",
            "ab.y",
            json!({"Ab": {"x": 1}, "aB": {"y": 2}}),
        ),
        // After pruning `Ab`, the target resolves to the null `aB`, which
        // can still take the value.
        (
            json!({"Ab": {"x": 1}, "aB": null}),
            "Ab.x",
            "ab.y",
            json!({"aB": {"y": 1}}),
        ),
        // The pruned subtree holds an array; rejecting the move puts it back.
        (
            json!({"Ab": [{"x": 1}], "aB": 0}),
            "Ab[0].x",
            "ab[0].y",
            json!({"Ab": [{"x": 1}], "aB": 0}),
        ),
        (
            json!({"o": {"Ab": [{"x": 1}], "aB": 0}}),
            "o.Ab[0].x",
            "o.ab[0].y",
            json!({"o": {"Ab": [{"x": 1}], "aB": 0}}),
        ),
        (
            json!({"rows": [{"old": 1}, {"old": 2}]}),
            "rows[1].old",
            "other.z",
            json!({"rows": [{"old": 1}, null], "other": {"z": 2}}),
        ),
    ] {
        let mut map = new_map();
        for (key, value) in input.as_object().unwrap() {
            map.insert(crate::Rc::from(key.as_str()), Value::from(value.clone()));
        }
        path::rename(&mut map, source, target, false);
        assert_eq!(
            make_value(map),
            Value::from(expected),
            "{source} -> {target}"
        );
    }
}

/// The previous `rename`: remove and write on a full copy of the map.
fn staged_rename(map: &ObjMap, source: &str, target: &str) -> ObjMap {
    let (source, target) = (segments(source), segments(target));
    if path::equivalent(&source, &target)
        || path::get_map(map, &target).is_some()
        || !path::can_set(map, &target)
    {
        return map.clone();
    }
    let Some(value) = path::get_map(map, &source).cloned() else {
        return map.clone();
    };
    let mut staged = map.clone();
    path::remove(&mut staged, &source);
    if path::get_map(&staged, &target).is_some() || !path::can_set(&staged, &target) {
        return map.clone();
    }
    path::set(&mut staged, &target, value, false);
    staged
}

#[test]
fn rename_matches_remove_then_set() {
    let inputs = [
        json!({"a": {"b": [null, {"c": 1}], "d": 2}, "A": 0}),
        json!({"a": [[{"x": 1}], null], "B": {"y": null}}),
        json!({"Ab": [{"x": 1, "w": 3}], "aB": [null, {"y": 2}], "c": null}),
        json!({"o": {"Ab": [{"x": [1]}], "aB": {"x": 4}}}),
    ];
    let paths = [
        "a",
        "A",
        "a.b",
        "a.b[1].c",
        "a.b[0]",
        "a.d",
        "a[0][0].x",
        "a[1]",
        "B.y",
        "Ab[0].x",
        "Ab[0].w",
        "aB[1].y",
        "ab[0].y",
        "ab.y",
        "c",
        "c.z",
        "o.Ab[0].x[0]",
        "o.ab[0].x",
        "o.aB.x",
        "o.ab.z",
        "n[2].m",
    ];
    for input in inputs {
        let map = map_of(input);
        for source in paths {
            for target in paths {
                let mut renamed = map.clone();
                path::rename(&mut renamed, source, target, false);
                assert_eq!(
                    make_value(renamed),
                    make_value(staged_rename(&map, source, target)),
                    "{source} -> {target} in {:?}",
                    make_value(map.clone())
                );
            }
        }
    }
}

#[test]
fn rename_moves_in_place() {
    let mut map = map_of(json!({"rows": [{"old": 1}, {"old": 2}]}));
    let rows =
        |current: &ObjMap| core::ptr::from_ref(current.get("rows").unwrap().as_array().unwrap());
    let before = rows(&map);
    path::rename(&mut map, "rows[0].old", "rows[0].new", false);
    assert_eq!(
        make_value(map.clone()),
        Value::from(json!({"rows": [{"new": 1}, {"old": 2}]}))
    );
    assert_eq!(rows(&map), before, "the rows array was copied");
}

#[test]
fn set_reports_whether_the_write_landed() {
    for (input, target, landed, expected) in [
        (json!({"a": [1]}), "a[0].k", false, json!({"a": [1]})),
        (json!({"a": "s"}), "a.b", false, json!({"a": "s"})),
        (
            json!({"a": null}),
            "a[1].k",
            true,
            json!({"a": [null, {"k": 9}]}),
        ),
        (json!({}), "x.y[0]", true, json!({"x": {"y": [9]}})),
    ] {
        let mut map = map_of(input);
        assert_eq!(
            path::set(&mut map, &segments(target), Value::from(9), false),
            landed,
            "{target}"
        );
        assert_eq!(make_value(map), Value::from(expected), "{target}");
    }
}

#[test]
fn index_bound_is_inclusive_at_max() {
    assert!(path::scalar_segments("a[4095]").is_some());
    assert!(path::scalar_segments("a[4096]").is_none());
    let mut map = new_map();
    path::set(
        &mut map,
        &path::scalar_segments("a[4095]").unwrap(),
        Value::from(1),
        false,
    );
    let value = make_value(map);
    let array = value
        .as_object()
        .unwrap()
        .get(&Value::from("a"))
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(array.len(), 4096);
}

#[test]
fn case_variant_keys_resolve_to_smallest_match() {
    for _ in 0..8 {
        let map = map_of(json!({"aB": 2, "Ab": 1}));
        assert_eq!(path::get_map(&map, &segments("ab")), Some(&Value::from(1)));
        let mut removed = map.clone();
        path::remove(&mut removed, &segments("AB"));
        assert_eq!(make_value(removed), Value::from(json!({"aB": 2})));
        let mut written = map;
        path::set(&mut written, &segments("ab"), Value::from(3), false);
        assert_eq!(make_value(written), Value::from(json!({"Ab": 3, "aB": 2})));
    }
}

#[test]
fn set_rejects_wildcards_without_writing() {
    let wildcard = path::parse("a[*].b").unwrap();
    let mut map = new_map();
    path::set(&mut map, &wildcard.segments, Value::from(1), false);
    assert_eq!(make_value(map), Value::from(json!({})));
    let mut object = Value::from(json!({}));
    path::set_object(
        object.as_object_mut().unwrap(),
        &wildcard.segments,
        Value::from(1),
        false,
    );
    assert_eq!(object, Value::from(json!({})));
}

#[test]
fn exact_key_wins_over_case_variant() {
    let map = map_of(json!({"Ab": 1, "ab": 2}));
    assert_eq!(path::get_map(&map, &segments("ab")), Some(&Value::from(2)));
    let mut written = map;
    path::set(&mut written, &segments("ab"), Value::from(3), false);
    assert_eq!(make_value(written), Value::from(json!({"Ab": 1, "ab": 3})));
    let mut object = Value::from(json!({"Ab": 1, "ab": 2}));
    assert_eq!(
        path::get(&object, &segments("ab"), true),
        Some(&Value::from(2))
    );
    let inner = object.as_object_mut().unwrap();
    path::set_object(inner, &segments("ab"), Value::from(3), false);
    path::remove_object(inner, &segments("Ab"), true);
    assert_eq!(object, Value::from(json!({"ab": 3})));
}

#[test]
fn unpruned_array_removal_keeps_nulls() {
    let mut object = Value::from(json!({"a": [1]}));
    assert!(!path::remove_object(
        object.as_object_mut().unwrap(),
        &segments("a[0]"),
        false
    ));
    assert_eq!(object, Value::from(json!({"a": [null]})));
}

#[test]
fn rename_lowercases_new_keys() {
    let mut map = map_of(json!({"a": 1}));
    path::rename(&mut map, "a", "New.Key", true);
    assert_eq!(make_value(map), Value::from(json!({"new": {"key": 1}})));
}

fn registry(resource_type: &str, aliases: &[(&str, &str)]) -> AliasRegistry {
    let entries: vec::Vec<_> = aliases
        .iter()
        .map(|(short, arm)| {
            json!({"name": alloc::format!("{resource_type}/{short}"), "defaultPath": arm})
        })
        .collect();
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
fn set_keys_uses_exact_keys_and_refuses_non_objects() {
    let mut map = map_of(json!({"Config": {"a": 1}, "n": null, "s": 3}));
    assert!(path::set_keys(
        &mut map,
        &segments("config.B"),
        Value::from(2),
        true
    ));
    for blocked in ["n.x", "s.x", "n.x.y"] {
        assert!(!path::set_keys(
            &mut map,
            &segments(blocked),
            Value::from(4),
            false
        ));
    }
    assert_eq!(
        make_value(map),
        Value::from(json!({"Config": {"a": 1}, "config": {"b": 2}, "n": null, "s": 3}))
    );
}

#[test]
fn non_dotted_alias_paths_stay_literal_keys() {
    let literal = |text: &str| vec![Segment::Key(crate::Rc::from(text))];
    assert_eq!(path::alias_segments("a.b"), segments("a.b"));
    assert_eq!(path::alias_segments("['a']"), literal("['a']"));
    assert_eq!(path::alias_segments("a[0]"), literal("a[0]"));
    assert_eq!(
        path::alias_segments("x. legacy"),
        vec![Segment::Key("x".into()), Segment::Key(" legacy".into())]
    );
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
fn unsuccessful_writes_preserve_short_value() {
    for arm in ["properties", "properties.target.x"] {
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
    assert_eq!(
        denorm(
            &[("z", "properties.target"), ("b.x", "properties.target.x")],
            json!({"z": 1, "b": {"x": 2}})
        ),
        Value::from(json!({"properties": {"target": 1, "b": {"x": 2}}}))
    );
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
    let raw = Value::from(json!({"type": "Test.Data/widgets", "x": {"b": 1, "sibling": 2}}));
    let normalized = normalizer::normalize(&raw, Some(&registry), None);
    assert_eq!(
        normalized,
        Value::from(
            json!({"a": {"b": 1}, "type": "Test.Data/widgets", "x": {"b": 1, "sibling": 2}})
        )
    );
    assert_eq!(registry.denormalize(&normalized, None), raw);
}

#[test]
fn dotted_aliases_round_trip() {
    round_trip(
        &[("Config.a", "properties.config.a")],
        json!({"type": "Test/widgets", "properties": {"Config": {"a": 1, "b": 2}}}),
        Some(json!({"config": {"a": 1, "b": 2}, "type": "Test/widgets"})),
    );
    round_trip(
        &[("a", "properties.b"), ("b", "properties.c")],
        json!({"type": "Test/widgets", "properties": {"b": 1, "c": 2}}),
        Some(json!({"a": 1, "b": 2, "c": 2, "type": "Test/widgets"})),
    );
    round_trip(
        &[("a.x", "properties.b.x"), ("b.x", "properties.c.x")],
        json!({"type": "Test/widgets", "properties": {"b": {"x": 1, "sibling": 3}, "c": {"x": 2}}}),
        None,
    );
}

/// Normalized data at an alias's short path is read as the alias value, as
/// Azure Policy's `field()` reads it, even when the ARM resource had a raw
/// field there; telling the two apart is A28.
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
fn reverse_leaf_remaps_precede_base_renames() {
    let aliases = [
        ("myrules[*]", "properties.rules[*]"),
        ("myrules[*].x", "properties.rules[*].y"),
    ];
    assert_eq!(
        denorm(&aliases, json!({"myrules": [{"x": 1}]})),
        Value::from(json!({"properties": {"rules": [{"y": 1}]}}))
    );
    assert_eq!(
        denorm(
            &[("renamed[*].leaf", "properties.original[*].arm")],
            json!({"renamed": [{"leaf": 1, "other": 2}]})
        ),
        Value::from(json!({"properties": {"original": [{"arm": 1, "other": 2}]}}))
    );
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
    for parent in [json!(5), json!(null)] {
        round_trip(
            &[("rules[*].display.name", "properties.rules[*].target.x")],
            json!({"type": "Test/widgets", "properties": {"rules": [{"target": {"x": "v"}, "display": parent}]}}),
            Some(
                json!({"type": "Test/widgets", "rules": [{"target": {"x": "v"}, "display": parent}]}),
            ),
        );
    }
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
    // A non-object value cannot replace `properties`.
    assert_eq!(
        denorm(&[("x", "properties")], json!({"x": 5, "a": 1})),
        Value::from(json!({"properties": {"a": 1}}))
    );
    for value in [json!(null), json!(5)] {
        round_trip(
            &[("x", "properties")],
            json!({"type": "Test/widgets", "properties": value}),
            Some(json!({"type": "Test/widgets", "x": value})),
        );
    }
}

#[test]
fn root_field_short_path_is_not_moved() {
    // The normalizer merges into the root field, so a value there may be the
    // resource's own.
    round_trip(
        &[("sku.name", "properties.sku.name")],
        json!({"type": "Test/widgets", "sku": {"name": "S", "tier": "t"}}),
        Some(json!({"type": "Test/widgets", "sku": {"name": "S", "tier": "t"}})),
    );
    assert_eq!(
        denorm(
            &[("sku.name", "properties.hardwareProfile.vmSize")],
            json!({"sku": {"name": "D2"}})
        ),
        Value::from(json!({"sku": {"name": "D2"}}))
    );
}

#[test]
fn dotted_base_of_other_aliases_is_not_moved() {
    for (aliases, raw, expected) in [
        (
            [
                ("a.b", "properties.x.y"),
                ("a.b[*].c", "properties.x.y[*].d"),
            ],
            json!({"x": {"y": [{"d": 1}]}}),
            json!({"a": {"b": [{"d": 1}]}, "x": {"y": [{"d": 1}]}}),
        ),
        (
            [
                ("cfg.list", "properties.cfg.items"),
                ("cfg.list[*].f", "properties.cfg.items[*].g"),
            ],
            json!({"cfg": {"items": [{"g": 1}]}}),
            json!({"cfg": {"items": [{"g": 1}], "list": [{"g": 1}]}}),
        ),
        (
            [
                ("cfg.data", "properties.config"),
                (
                    "cfg.data.rules[*].x",
                    "properties.config.rules[*].properties.x",
                ),
            ],
            json!({"config": {"rules": [{"properties": {"x": 1}}]}}),
            json!({
                "cfg": {"data": {"rules": [{"properties": {"x": 1}}]}},
                "config": {"rules": [{"properties": {"x": 1}}]}
            }),
        ),
    ] {
        let registry = registry("Test/widgets", &aliases);
        let raw = Value::from(json!({"type": "Test/widgets", "properties": raw}));
        let normalized = normalizer::normalize(&raw, Some(&registry), None);
        assert_eq!(
            registry.denormalize(&normalized, None),
            Value::from(json!({"type": "Test/widgets", "properties": expected})),
            "{aliases:?}"
        );
    }
}

#[test]
fn dotted_and_non_dotted_paths_meet() {
    let raw = json!({"type": "Test/widgets", "properties": {"a": {"b": 1}}});
    for arm in ["properties.x[0]", "properties['a.b']"] {
        round_trip(
            &[("a.b", arm)],
            raw.clone(),
            Some(json!({"type": "Test/widgets", "a": {"b": 1}})),
        );
    }
    round_trip(
        &[("['a']", "properties.x.y")],
        json!({"type": "Test/widgets", "properties": {"x": {"y": 1, "z": 2}}}),
        Some(json!({"type": "Test/widgets", "['a']": 1, "x": {"y": 1, "z": 2}})),
    );
    let mut versioned = AliasRegistry::new();
    versioned
        .load_from_json(
            &json!([{"namespace": "Test", "resourceTypes": [{"resourceType": "widgets", "aliases": [{
                "name": "Test/widgets/a.b",
                "defaultPath": "properties.x.b",
                "paths": [{"path": "properties.x[0]", "apiVersions": ["2024-01-01"]}]
            }]}]}])
            .to_string(),
        )
        .unwrap();
    for (version, normalized) in [
        (
            None,
            json!({"type": "Test/widgets", "a": {"b": 1}, "x": {"b": 1}}),
        ),
        (
            Some("2024-01-01"),
            json!({"type": "Test/widgets", "a": {"b": 1}}),
        ),
    ] {
        let raw = Value::from(match version {
            None => json!({"type": "Test/widgets", "properties": {"x": {"b": 1}}}),
            Some(_) => raw.clone(),
        });
        let actual = normalizer::normalize(&raw, Some(&versioned), version);
        assert_eq!(actual, Value::from(normalized), "{version:?}");
        assert_eq!(versioned.denormalize(&actual, version), raw, "{version:?}");
    }
    let entries = &versioned.get("Test/widgets").unwrap().entries;
    assert!(entries["a.b"].nested_short_name);
    for (short, dotted) in [
        ("a.b", true),
        ("a", true),
        ("['a']", false),
        ("x. legacy", false),
        ("a[0]", false),
    ] {
        let single = registry("Test/widgets", &[(short, "properties.x")]);
        let entry = single
            .get("Test/widgets")
            .unwrap()
            .entries
            .values()
            .next()
            .unwrap();
        assert_eq!(entry.nested_short_name, dotted, "{short}");
    }
}

#[test]
fn moves_skip_paths_other_phases_own() {
    // A bracketed spelling of the short name still extends it.
    round_trip(
        &[
            ("a.b", "properties.x.y"),
            ("a['b'][*].c", "properties.x.y[*].d"),
        ],
        json!({"type": "Test/widgets", "properties": {"a": {"b": [{"d": 1}]}, "x": {"y": [{"d": 1}]}}}),
        None,
    );
    // A collision key is phase 2a's to rename.
    round_trip(
        &[("_p_sku.name", "properties.foo"), ("sku", "properties.sku")],
        json!({"type": "Test/widgets", "sku": {"name": "S"}, "properties": {"sku": {"name": "S"}}}),
        None,
    );
    // Root fields stay on the data plane too.
    let registry = registry(
        "Test.Data/widgets",
        &[("SKU.name", "properties.hardwareProfile.vmSize")],
    );
    let raw = Value::from(json!({"type": "Test.Data/widgets", "sku": {"name": "D2"}}));
    let normalized = normalizer::normalize(&raw, Some(&registry), None);
    assert_eq!(registry.denormalize(&normalized, None), raw);
}
