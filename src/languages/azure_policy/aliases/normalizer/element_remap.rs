// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Element-level field remapping for array aliases with versioned paths.

use alloc::string::String;
use alloc::vec::Vec;

use crate::value::Object;
use crate::Value;

use super::super::obj_map::{obj_get_mut_ci, object_get_ci, object_get_mut_ci, ObjMap};
use super::super::path::{self, Segment};
use super::super::types::PrecomputedRemap;

/// Describes a field remapping inside each element of a (possibly nested) array.
pub struct ElementRemap {
    /// Chain of array navigations for nested `[*]` levels.
    pub(crate) array_chain: Vec<Vec<String>>,
    /// Path to read within the innermost array element, matching keys
    /// ignoring ASCII case.
    pub(crate) source_field: Vec<Segment>,
    /// Path to write within the innermost array element, with exact keys.
    pub(crate) target_field: Vec<Segment>,
}

/// Apply an element-level field remap to each element of an array (or nested
/// array chain). The value is moved: the source is removed (keeping the
/// containers it empties) and the target written. A source that a target
/// overlaps is removed first, so a target nested under its own source path
/// (`cfg` to `cfg.value`) is not deleted with it. Otherwise an element whose
/// target path runs through a non-object, `null` included, keeps its source.
///
/// When `lowercase` is `true` (normalizer), target path segments are
/// lowercased.  When `false` (denormalizer), they are written verbatim
/// so that restored casing is preserved.
pub fn apply_element_remap(result: &mut ObjMap, remap: &ElementRemap, lowercase: bool) {
    apply_remap_at_depth(
        result,
        &remap.array_chain,
        0,
        &remap.source_field,
        &remap.target_field,
        lowercase,
    );
}

/// Apply a precomputed element remap (from [`PrecomputedRemap`]).
pub fn apply_element_remap_precomputed(result: &mut ObjMap, remap: &PrecomputedRemap) {
    apply_remap_at_depth(
        result,
        &remap.array_chain,
        0,
        &path::alias_segments(&remap.source_field),
        &path::alias_segments(&remap.target_field),
        true,
    );
}

/// Recursively navigate nested arrays via `array_chain` and apply a field
/// remap in each innermost element.
fn apply_remap_at_depth(
    obj: &mut ObjMap,
    array_chain: &[Vec<String>],
    depth: usize,
    source_field: &[Segment],
    target_field: &[Segment],
    lowercase: bool,
) {
    // Element remaps always have an array to enter.
    let Some(nav) = array_chain.get(depth) else {
        return;
    };

    let first = match nav.first() {
        Some(f) => f.as_str(),
        None => return,
    };

    // Navigate through intermediate segments to reach the array value.
    let arr_val = if nav.len() == 1 {
        match obj_get_mut_ci(obj, first) {
            Some(v) => v,
            None => return,
        }
    } else {
        let mut cur: &mut Value = match obj_get_mut_ci(obj, first) {
            Some(v) => v,
            None => return,
        };
        for segment in nav.iter().skip(1) {
            cur = match cur.as_object_mut() {
                Ok(inner) => match object_get_mut_ci(inner, segment) {
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
                    source_field,
                    target_field,
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
    source_field: &[Segment],
    target_field: &[Segment],
    lowercase: bool,
) {
    let Some(nav) = array_chain.get(depth) else {
        remap_deep_field_in_btree(btree, source_field, target_field, lowercase);
        return;
    };

    let first = match nav.first() {
        Some(f) => f.as_str(),
        None => return,
    };

    let arr_val = if nav.len() == 1 {
        match object_get_mut_ci(btree, first) {
            Some(v) => v,
            None => return,
        }
    } else {
        let mut cur: &mut Value = match object_get_mut_ci(btree, first) {
            Some(v) => v,
            None => return,
        };
        for segment in nav.iter().skip(1) {
            cur = match cur.as_object_mut() {
                Ok(inner) => match object_get_mut_ci(inner, segment) {
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
                    source_field,
                    target_field,
                    lowercase,
                );
            }
        }
    }
}

/// Move a value between paths inside one array element.
fn remap_deep_field_in_btree(
    btree: &mut Object,
    source: &[Segment],
    target: &[Segment],
    lowercase: bool,
) {
    let Some((Segment::Key(first), rest)) = source.split_first() else {
        return;
    };
    let Some(val) = object_get_ci(btree, first).and_then(|value| path::get(value, rest, true))
    else {
        return;
    };
    let val = val.clone();
    // A target overlapping its source is cleared by removing the source.
    let overlap = source.len().min(target.len());
    let overlaps = matches!(
        (source.get(..overlap), target.get(..overlap)),
        (Some(source), Some(target)) if path::equivalent(source, target)
    );
    if overlaps || path::can_set_object_keys(btree, target, lowercase) {
        path::remove_object(btree, source, false);
        path::set_object_keys(btree, target, val, lowercase);
    }
}
