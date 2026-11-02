// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Lightweight string-keyed map used during normalization/denormalization.
//!
//! Internally uses `hashbrown::HashMap<Rc<str>, Value>` for O(1) lookups,
//! then converts to `Value::Object` (an `Object`) only at
//! the output boundary via [`make_value`].

use alloc::string::String;
use alloc::vec::Vec;

use hashbrown::HashMap;

use crate::value::Object;
use crate::Rc;
use crate::Value;

/// A string-keyed map of JSON values.
///
/// All normalizer / denormalizer code works with this type internally.
/// Convert to [`Value::Object`] via [`make_value`] when producing output.
pub type ObjMap = HashMap<Rc<str>, Value>;

/// Create an empty [`ObjMap`].
pub fn new_map() -> ObjMap {
    ObjMap::new()
}

/// Look up a value by string key.
pub fn obj_get<'a>(map: &'a ObjMap, key: &str) -> Option<&'a Value> {
    map.get(key)
}

/// Look up a mutable value reference by string key.
pub fn obj_get_mut<'a>(map: &'a mut ObjMap, key: &str) -> Option<&'a mut Value> {
    map.get_mut(key)
}

/// Insert a key-value pair.
pub fn obj_insert(map: &mut ObjMap, key: &str, val: Value) {
    map.insert(Rc::from(key), val);
}

/// Insert a key-value pair using a pre-allocated `Rc<str>` key.
///
/// Avoids the `Rc::from(key)` heap allocation that [`obj_insert`] performs.
pub fn obj_insert_rc(map: &mut ObjMap, key: Rc<str>, val: Value) {
    map.insert(key, val);
}

/// Check whether a key exists.
pub fn obj_contains(map: &ObjMap, key: &str) -> bool {
    map.contains_key(key)
}

/// Convert an [`ObjMap`] into a [`Value::Object`].
///
/// Keys are converted from `Rc<str>` to `Value::String` and inserted into
/// an `Object` to match the `Value::Object` representation.
pub fn make_value(map: ObjMap) -> Value {
    let obj: Object = map
        .into_iter()
        .map(|(k, v)| (Value::String(k), v))
        .collect();
    Value::Object(Rc::new(obj))
}

/// Convert a `Vec<Value>` into a `Value::Array`.
pub fn make_array(items: Vec<Value>) -> Value {
    Value::from_array(items)
}

/// Extract a `&str` from a `Value::String`.
pub fn val_str(v: &Value) -> Option<&str> {
    match v {
        Value::String(s) => Some(s.as_ref()),
        _ => None,
    }
}

/// Extract the `type` field value from a resource JSON object.
///
/// Performs a case-insensitive key lookup so both `"type"` and `"Type"` work.
pub fn extract_type_field(resource: &Value) -> Option<&str> {
    resource.as_object().ok().and_then(|obj| {
        obj.iter()
            .find(|(k, _)| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case("type")))
            .and_then(|(_, v)| val_str(v))
    })
}

/// Convert a `Value::Object` (Object) into an [`ObjMap`].
///
/// Non-string keys are silently skipped.
#[allow(dead_code)]
pub fn value_to_obj_map(value: &Value) -> Option<ObjMap> {
    let obj = value.as_object().ok()?;
    let mut map = ObjMap::with_capacity(obj.len());
    for (k, v) in obj.iter() {
        if let Value::String(s) = k {
            map.insert(Rc::clone(s), v.clone());
        }
    }
    Some(map)
}

/// Set a value at a dotted or bracket path in an [`ObjMap`], creating
/// intermediate containers as needed.  All keys are lowercased.  Paths that
/// do not parse are ignored.
pub fn set_nested_lowercased(result: &mut ObjMap, path: &str, value: Value) {
    if let Some(segments) = super::path::scalar_segments(path) {
        super::path::set(result, &segments, value, true);
    }
}

/// Fields that exist at the ARM resource root (not under `properties`).
///
/// These are the standard ARM resource envelope fields as defined by the
/// Azure Resource Manager resource model.  They are preserved at the
/// resource root during normalization and denormalization.
pub const ROOT_FIELDS: &[&str] = &[
    "name",
    "type",
    "location",
    "kind",
    "id",
    "tags",
    "identity",
    "sku",
    "plan",
    "zones",
    "managedBy",
    "etag",
    "apiVersion",
    "fullName",
    "systemData",
    "extendedLocation",
];

/// Check whether an alias short name collides with a reserved ARM root field
/// and needs a collision-safe key.
pub fn is_root_field_collision(short_name: &str, default_path: &str) -> bool {
    let Some(short) = super::path::scalar_segments(short_name) else {
        return false;
    };
    let Some(arm) = super::path::scalar_segments(default_path) else {
        return false;
    };
    let [super::path::Segment::Key(short)] = short.as_slice() else {
        return false;
    };
    ROOT_FIELDS.iter().any(|f| f.eq_ignore_ascii_case(short))
        && super::path::without_properties(&arm).len() < arm.len()
        && arm.len() > 1
}

/// Return a collision-safe key for an alias whose short name collides with a
/// root ARM field.  The key is `_p_` + the lowercased short name.
pub fn collision_safe_key(short_name: &str) -> String {
    if let Some(segments) = super::path::scalar_segments(short_name) {
        if let [super::path::Segment::Key(key)] = segments.as_slice() {
            return alloc::format!("_p_{}", key.to_ascii_lowercase());
        }
    }
    alloc::format!("_p_{}", short_name.to_ascii_lowercase())
}
