// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Element-level field remapping for array aliases with versioned paths.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use crate::value::Object;
use crate::{Rc, Value};

use super::super::obj_map::{obj_get_mut_ci, object_get_mut_ci, ObjMap};
use super::super::path::{self, Segment};
use super::super::types::ElementMove;

/// How [`apply_element_plan`] applies an element plan.
#[derive(Debug, Clone, Copy)]
pub struct Direction<'a> {
    /// `None` to normalize (each ARM source becomes its alias target). To
    /// denormalize, the casing to restore on the ARM keys written back.
    pub casing: Option<&'a BTreeMap<String, String>>,
    /// Whether keys are looked up exactly rather than in any ASCII case.
    pub exact: bool,
    /// If set, skip the alias leaves whose arrays are elsewhere.
    pub at_root: Option<bool>,
}

/// Apply element `moves` to each element of the array at `base` in `map`.
pub fn apply_element_plan(
    map: &mut ObjMap,
    base: &[String],
    moves: &[ElementMove],
    dir: Direction<'_>,
) {
    let Some((first, rest)) = base.split_first() else {
        return;
    };
    let found = if dir.exact {
        map.get_mut(first.as_str())
    } else {
        obj_get_mut_ci(map, first)
    };
    let Some(mut value) = found else {
        return;
    };
    for key in rest {
        value = match value.as_object_mut() {
            Ok(object) => match object_get_mut(object, key, dir.exact) {
                Some(child) => child,
                None => return,
            },
            Err(_) => return,
        };
    }
    apply_moves(value, moves, true, dir);
}

/// Apply `moves` to each element of an array value if `array`, otherwise to
/// an object value.
fn apply_moves(value: &mut Value, moves: &[ElementMove], array: bool, dir: Direction<'_>) {
    if moves.is_empty() {
        return;
    }
    match value {
        Value::Array(elements) if array => {
            for element in Rc::make_mut(elements).iter_mut() {
                rebuild(element, moves, dir);
            }
        }
        Value::Object(_) if !array => rebuild(value, moves, dir),
        _ => {}
    }
}

/// Rebuild one object from a snapshot of it. Every move reads the snapshot,
/// so it never sees another move's result: all sources are removed (pruning
/// the ARM parents they empty when normalizing), then each value is written
/// at its target. The targets are disjoint, so the order of writes only
/// matters when denormalizing: shallower ARM paths are written first, and
/// for an ARM path several aliases share, the first alias's value wins.
/// Fields no move reads pass through, unless a move writes over them.
fn rebuild(element: &mut Value, moves: &[ElementMove], dir: Direction<'_>) {
    let snapshot = element.clone();
    let Value::Object(object) = element else {
        return;
    };
    let object = Rc::make_mut(object);
    let reverse = dir.casing.is_some();
    let active = moves
        .iter()
        .filter(|m| dir.at_root.is_none() || m.at_root.is_none() || m.at_root == dir.at_root);
    let mut values: Vec<(&ElementMove, Value)> = Vec::new();
    for m in active {
        let (read, _) = ends(m, reverse);
        if m.source == m.target {
            // A nested array level (or a relative leaf) that keeps its name.
            if let Some(child) = child_mut(object, read, dir.exact) {
                apply_moves(child, &m.moves, m.implied, dir);
            }
        } else if let Some(value) = path::get(&snapshot, read, !dir.exact) {
            values.push((m, value.clone()));
            path::remove_object(object, read, !reverse);
        }
    }
    values.sort_by_key(|(m, _)| (ends(m, reverse).1.len(), m.order));
    let mut written: Vec<&[Segment]> = Vec::new();
    for (m, mut value) in values {
        let (read, write) = ends(m, reverse);
        if written.contains(&write) {
            continue;
        }
        apply_moves(&mut value, &m.moves, m.implied, dir);
        if path::set_object(object, &cased(write, dir.casing), value, !reverse) {
            written.push(write);
        } else if let Some(original) = path::get(&snapshot, read, !dir.exact) {
            // A non-object is in the way: keep the value where it was.
            path::set_object(object, &cased(read, dir.casing), original.clone(), !reverse);
        }
    }
}

/// The path a move reads and the path it writes.
fn ends(m: &ElementMove, reverse: bool) -> (&[Segment], &[Segment]) {
    if reverse {
        (&m.target, &m.source)
    } else {
        (&m.source, &m.target)
    }
}

/// `segments` with the casing restored, if any.
fn cased(segments: &[Segment], casing: Option<&BTreeMap<String, String>>) -> Vec<Segment> {
    segments
        .iter()
        .map(|segment| match (segment, casing) {
            (Segment::Key(key), Some(map)) => map.get(&**key).map_or_else(
                || segment.clone(),
                |restored| Segment::Key(restored.as_str().into()),
            ),
            _ => segment.clone(),
        })
        .collect()
}

/// The value at the object keys `segments` below `object`.
fn child_mut<'a>(
    object: &'a mut Object,
    segments: &[Segment],
    exact: bool,
) -> Option<&'a mut Value> {
    let Some((Segment::Key(first), rest)) = segments.split_first() else {
        return None;
    };
    let mut value = object_get_mut(object, first, exact)?;
    for segment in rest {
        let Segment::Key(key) = segment else {
            return None;
        };
        value = object_get_mut(value.as_object_mut().ok()?, key, exact)?;
    }
    Some(value)
}

/// Look up `key` exactly if `exact`, otherwise falling back to a key that
/// differs only in ASCII case.
fn object_get_mut<'a>(obj: &'a mut Object, key: &str, exact: bool) -> Option<&'a mut Value> {
    if exact {
        obj.get_mut(&Value::from(key))
    } else {
        object_get_mut_ci(obj, key)
    }
}
