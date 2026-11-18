// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Element-level field remapping for array aliases with versioned paths.

use alloc::string::String;
use alloc::vec::Vec;

use crate::value::Object;
use crate::Value;

use super::super::obj_map::{
    obj_get, obj_get_mut, obj_insert, remove_at_dotted_path_obj, remove_element_field, set_nested,
    set_nested_lowercased, set_nested_verbatim, ObjMap,
};

/// Move fields within each element of a (possibly nested) array: each
/// `(source, target)` pair moves the dot-separated `source` path to `target`.
///
/// Each source is taken in turn, but all targets are written afterwards, so
/// pairs that swap or chain field names don't read each other's results.
///
/// When `lowercase` is `true` (normalizer), target path segments are
/// lowercased.  When `false` (denormalizer), they are written verbatim
/// so that restored casing is preserved.
pub fn apply_element_remaps(
    result: &mut ObjMap,
    array_chain: &[Vec<String>],
    fields: &[(&str, &str)],
    lowercase: bool,
) {
    apply_remap_at_depth(result, array_chain, 0, fields, lowercase);
}

/// Recursively navigate nested arrays via `array_chain` and apply a field
/// remap in each innermost element.
fn apply_remap_at_depth(
    obj: &mut ObjMap,
    array_chain: &[Vec<String>],
    depth: usize,
    fields: &[(&str, &str)],
    lowercase: bool,
) {
    let Some(nav) = array_chain.get(depth) else {
        remap_fields(obj, fields, lowercase);
        return;
    };

    let first = match nav.first() {
        Some(f) => f.as_str(),
        None => return,
    };

    // Navigate through intermediate segments to reach the array value.
    let arr_val = if nav.len() == 1 {
        match obj_get_mut(obj, first) {
            Some(v) => v,
            None => return,
        }
    } else {
        let mut cur: &mut Value = match obj_get_mut(obj, first) {
            Some(v) => v,
            None => return,
        };
        for segment in nav.iter().skip(1) {
            cur = match cur.as_object_mut() {
                Ok(inner) => match inner.get_mut(&Value::from(segment.as_str())) {
                    Some(v) => v,
                    None => return,
                },
                Err(_) => return,
            };
        }
        cur
    };

    if let Value::Array(elements) = arr_val {
        let inner = crate::Rc::make_mut(elements);
        for elem in inner.iter_mut() {
            if let Value::Object(obj_rc) = elem {
                let inner_btree = crate::Rc::make_mut(obj_rc);
                remap_at_depth_in_btree(
                    inner_btree,
                    array_chain,
                    depth.saturating_add(1),
                    fields,
                    lowercase,
                );
            }
        }
    }
}

/// BTreeMap-native recursion for element-level remap, avoiding ObjMap
/// round-trips on each array element.
fn remap_at_depth_in_btree(
    btree: &mut Object,
    array_chain: &[Vec<String>],
    depth: usize,
    fields: &[(&str, &str)],
    lowercase: bool,
) {
    let Some(nav) = array_chain.get(depth) else {
        remap_fields_in_btree(btree, fields, lowercase);
        return;
    };

    let first = match nav.first() {
        Some(f) => f.as_str(),
        None => return,
    };

    let key_val = Value::from(first);
    let arr_val = if nav.len() == 1 {
        match btree.get_mut(&key_val) {
            Some(v) => v,
            None => return,
        }
    } else {
        let mut cur: &mut Value = match btree.get_mut(&key_val) {
            Some(v) => v,
            None => return,
        };
        for segment in nav.iter().skip(1) {
            cur = match cur.as_object_mut() {
                Ok(inner) => match inner.get_mut(&Value::from(segment.as_str())) {
                    Some(v) => v,
                    None => return,
                },
                Err(_) => return,
            };
        }
        cur
    };

    if let Value::Array(elements) = arr_val {
        let inner = crate::Rc::make_mut(elements);
        for elem in inner.iter_mut() {
            if let Value::Object(obj_rc) = elem {
                let inner_btree = crate::Rc::make_mut(obj_rc);
                remap_at_depth_in_btree(
                    inner_btree,
                    array_chain,
                    depth.saturating_add(1),
                    fields,
                    lowercase,
                );
            }
        }
    }
}

/// Take each pair's source value in turn, as moving them one by one would,
/// but leave the targets for the caller to write afterwards so no move reads
/// another's result. A source repeated from an earlier pair gets the same
/// value.
fn take_sources<'a>(
    fields: &[(&'a str, &'a str)],
    mut take: impl FnMut(&str) -> Option<Value>,
) -> Vec<(&'a str, Value)> {
    let mut taken: Vec<(&str, Value)> = Vec::new();
    let mut moved = Vec::new();
    for &(source, target) in fields {
        let val = match taken.iter().find(|(earlier, _)| *earlier == source) {
            Some((_, val)) => Some(val.clone()),
            None => {
                let val = take(source);
                if let Some(val) = &val {
                    taken.push((source, val.clone()));
                }
                val
            }
        };
        if let Some(val) = val {
            moved.push((target, val));
        }
    }
    moved
}

/// Move each `(source, target)` pair's value directly in a BTreeMap.
fn remap_fields_in_btree(btree: &mut Object, fields: &[(&str, &str)], lowercase: bool) {
    let moved = take_sources(fields, |source| {
        let val = read_dotted_path_btree(btree, source)?;
        let segments: Vec<&str> = source.split('.').collect();
        remove_at_dotted_path_obj(btree, &segments);
        Some(val)
    });
    for (target, val) in moved {
        let segments: Vec<&str> = target.split('.').collect();
        match segments.as_slice() {
            [] => {}
            [seg] => {
                btree.insert(Value::String(crate::Rc::from(*seg)), val);
            }
            _ => set_nested(btree, &segments, val, lowercase),
        }
    }
}

/// Read a value at a dotted path from a BTreeMap.
fn read_dotted_path_btree(btree: &Object, path: &str) -> Option<Value> {
    let segments: Vec<&str> = path.split('.').collect();
    let first = segments.first()?;
    let mut cur: &Value = btree.get(&Value::from(*first))?;
    for &seg in segments.iter().skip(1) {
        cur = cur.as_object().ok()?.get(&Value::from(seg))?;
    }
    Some(cur.clone())
}

/// Move each `(source, target)` pair's value in an ObjMap.  Used only at
/// the top level when `depth >= array_chain.len()`.
fn remap_fields(obj: &mut ObjMap, fields: &[(&str, &str)], lowercase: bool) {
    let moved = take_sources(fields, |source| {
        let val = read_dotted_path(obj, source)?;
        remove_element_field(obj, &[], source);
        Some(val)
    });
    for (target, val) in moved {
        if !target.contains('.') {
            obj_insert(obj, target, val);
        } else if lowercase {
            set_nested_lowercased(obj, target, val);
        } else {
            set_nested_verbatim(obj, target, val);
        }
    }
}

/// Read a value at a dot-separated path from an ObjMap.
fn read_dotted_path(obj: &ObjMap, path: &str) -> Option<Value> {
    let segments: Vec<&str> = path.split('.').collect();
    let first = segments.first()?;
    let mut cur: &Value = obj_get(obj, first)?;
    for &seg in segments.iter().skip(1) {
        cur = cur.as_object().ok()?.get(&Value::from(seg))?;
    }
    Some(cur.clone())
}
