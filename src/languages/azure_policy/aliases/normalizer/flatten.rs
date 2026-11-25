// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Value normalization helpers: recursive key lowercasing, sub-resource array
//! flattening, and element merging.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use crate::value::Object;
use crate::Value;

use super::super::obj_map::{
    collision_safe_key, is_element_envelope_field, make_array, make_value, new_map, obj_contains,
    obj_insert, set_nested_lowercased, take_dotted_path_obj, val_str,
};
use super::super::types::ElementFields;

/// Lowercase all keys of a JSON object (shallow — values are untouched).
/// Non-object values are returned as-is.
pub fn lowercase_object_keys(value: &Value) -> Value {
    match value {
        Value::Object(obj) => {
            let mut result = new_map();
            for (k, v) in obj.iter() {
                if let Some(s) = val_str(k) {
                    obj_insert(&mut result, &s.to_ascii_lowercase(), v.clone());
                }
            }
            make_value(result)
        }
        _ => value.clone(),
    }
}

/// What flattening needs to know about a resource type's aliases.
pub struct Flatten<'a> {
    /// The sub-resource arrays, by lowercase dotted name.
    pub sub_arrays: &'a BTreeSet<String>,
    /// The aliased fields of each sub-resource array's elements.
    pub fields: &'a BTreeMap<String, ElementFields>,
}

/// Recursively normalize a value, flattening sub-resource array elements.
pub fn normalize_value(value: &Value, field_path: &str, cx: Option<&Flatten<'_>>) -> Value {
    match value {
        Value::Array(arr) => {
            let items: Vec<Value> = if is_sub_resource_array(field_path, cx) {
                arr.iter()
                    .map(|elem| flatten_element(elem, field_path, cx))
                    .collect()
            } else {
                arr.iter()
                    .map(|elem| normalize_value(elem, field_path, cx))
                    .collect()
            };
            make_array(items)
        }
        Value::Object(obj) => {
            let mut result = new_map();
            for (k, v) in obj.iter() {
                let key_s = match val_str(k) {
                    Some(s) => s,
                    None => continue,
                };
                let child_path = alloc::format!("{}.{}", field_path, key_s);
                obj_insert(
                    &mut result,
                    &key_s.to_ascii_lowercase(),
                    normalize_value(v, &child_path, cx),
                );
            }
            make_value(result)
        }
        _ => value.clone(),
    }
}

/// Flatten a sub-resource array element by merging its `properties` into
/// the element root.
///
/// Aliased fields are first moved to their short names from where their
/// aliases read them, inside or outside the wrapper, so a wrapped and an
/// unwrapped field with one ARM name stay apart. A wrapped field whose name
/// the element root already has, or which an alias reads outside the wrapper,
/// is kept as `_p_<name>`, as is any field already named `_p_*`; a standard
/// envelope field (`name`) at the root wins over a wrapped one.
pub fn flatten_element(element: &Value, array_path: &str, cx: Option<&Flatten<'_>>) -> Value {
    let obj = match element.as_object() {
        Ok(o) => o,
        Err(_) => return element.clone(),
    };

    let mut envelope = obj.clone();
    let mut props = Object::new();
    let wrappers: Vec<Value> = obj
        .keys()
        .filter(|k| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case("properties")))
        .cloned()
        .collect();
    for (i, key) in wrappers.iter().enumerate() {
        if let Some(Value::Object(inner)) = envelope.remove(key) {
            if i == 0 {
                props = (*inner).clone();
            }
        }
    }

    let fields = cx.and_then(|cx| cx.fields.get(&array_path.to_ascii_lowercase()));
    let mut moved = Vec::new();
    for field in fields.iter().flat_map(|fields| &fields.fields) {
        let source = if field.wrapped {
            &mut props
        } else {
            &mut envelope
        };
        if let Some(value) = take_dotted_path_obj(source, &field.arm) {
            let child_path = alloc::format!("{}.{}", array_path, field.short);
            moved.push((field, normalize_value(&value, &child_path, cx)));
        }
    }

    let mut result = new_map();
    for (key, val) in envelope.iter() {
        let Some(key_s) = val_str(key) else {
            continue;
        };
        let child_path = alloc::format!("{}.{}", array_path, key_s);
        let mut lc_key = key_s.to_ascii_lowercase();
        // Escape raw `_p_` names so re-wrapping decodes them losslessly.
        if lc_key.starts_with("_p_") {
            lc_key = collision_safe_key(&lc_key);
        }
        obj_insert(&mut result, &lc_key, normalize_value(val, &child_path, cx));
    }

    for (key, val) in props.iter() {
        let Some(key_s) = val_str(key) else {
            continue;
        };
        let lc_key = key_s.to_ascii_lowercase();
        let child_path = alloc::format!("{}.{}", array_path, key_s);
        let val = normalize_value(val, &child_path, cx);
        // An aliased field owns its name, and writes into an object on its
        // dotted path.
        let replaced = fields
            .iter()
            .flat_map(|fields| &fields.fields)
            .any(|field| {
                field.short == lc_key
                    || (field.short.starts_with(lc_key.as_str())
                        && field.short.as_bytes().get(lc_key.len()) == Some(&b'.')
                        && !matches!(val, Value::Object(_)))
            });
        let at_root = fields.is_some_and(|fields| fields.root.contains(&lc_key));
        if at_root || replaced || lc_key.starts_with("_p_") || obj_contains(&result, &lc_key) {
            if obj_contains(&result, &lc_key) && is_element_envelope_field(&lc_key) {
                continue;
            }
            obj_insert(&mut result, &collision_safe_key(&lc_key), val);
        } else {
            obj_insert(&mut result, &lc_key, val);
        }
    }

    for (field, value) in moved {
        set_nested_lowercased(&mut result, &field.short, value);
    }

    make_value(result)
}

/// Check if a field path corresponds to a sub-resource array.
fn is_sub_resource_array(field_path: &str, cx: Option<&Flatten<'_>>) -> bool {
    cx.is_some_and(|cx| cx.sub_arrays.contains(&field_path.to_ascii_lowercase()))
}
