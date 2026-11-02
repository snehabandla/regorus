// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Alias-local path grammar. Quotes have no escapes and close only before
//! optional whitespace and `]`; delimiters inside quoted keys are literal.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use crate::{value::Object, Rc, Value};

use super::obj_map::{make_array, make_value, new_map, ObjMap};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Segment {
    Key(Rc<str>),
    Index(usize),
    Wildcard,
}

/// Bound sparse catalog writes to at most 4096 array elements.
pub const MAX_INDEX: usize = 4095;

pub struct Path {
    pub segments: Vec<Segment>,
    wildcards: Vec<(usize, usize)>,
}

pub fn parse(path: &str) -> Option<Path> {
    let mut segments = Vec::new();
    let mut wildcards = Vec::new();
    let mut pos = 0_usize;
    loop {
        let start = pos;
        let (segment, end) = if path.as_bytes().get(pos) == Some(&b'[') {
            bracket(path, pos)?
        } else {
            let end = path
                .get(pos..)?
                .find(['.', '['])
                .map_or(path.len(), |offset| pos.saturating_add(offset));
            let key = path.get(pos..end)?.trim();
            if key.is_empty() || key.contains(']') {
                return None;
            }
            (Segment::Key(Rc::from(key)), end)
        };
        if segment == Segment::Wildcard {
            wildcards.push((start, end));
        }
        segments.push(segment);
        pos = end;
        match path.as_bytes().get(pos) {
            None => {
                return Some(Path {
                    segments,
                    wildcards,
                })
            }
            Some(b'.') => {
                pos = pos.saturating_add(1);
                if pos == path.len() {
                    return None;
                }
            }
            Some(b'[') => {}
            _ => return None,
        }
    }
}

fn bracket(path: &str, open: usize) -> Option<(Segment, usize)> {
    let body_start = open.saturating_add(1);
    let body = path.get(body_start..)?;
    let trimmed = body.trim_start();
    if let Some(quote @ (b'\'' | b'"')) = trimmed.as_bytes().first() {
        let content_start = body_start
            .saturating_add(body.len().saturating_sub(trimmed.len()))
            .saturating_add(1);
        let mut search = content_start;
        while let Some(offset) = path.get(search..)?.find(char::from(*quote)) {
            let close = search.saturating_add(offset);
            let after = path.get(close.saturating_add(1)..)?;
            let tail = after.trim_start();
            if tail.starts_with(']') {
                let key = path.get(content_start..close)?;
                if key.is_empty() {
                    return None;
                }
                let end = close
                    .saturating_add(1)
                    .saturating_add(after.len().saturating_sub(tail.len()))
                    .saturating_add(1);
                return Some((Segment::Key(Rc::from(key)), end));
            }
            search = close.saturating_add(1);
        }
    }

    // Match field/binding paths: an unmatched opening quote is literal.
    let close = body.find(']')?;
    let raw = body.get(..close)?;
    let key = raw.trim();
    if key.is_empty() || key.contains('[') {
        return None;
    }
    let segment = if raw == "*" {
        Segment::Wildcard
    } else if key.bytes().all(|byte| byte.is_ascii_digit()) {
        let index = key.parse().ok()?;
        if index > MAX_INDEX {
            return None;
        }
        Segment::Index(index)
    } else {
        Segment::Key(Rc::from(key))
    };
    Some((segment, body_start.saturating_add(close).saturating_add(1)))
}

pub fn scalar_segments(path: &str) -> Option<Vec<Segment>> {
    let parsed = parse(path)?;
    parsed.wildcards.is_empty().then_some(parsed.segments)
}

pub fn equivalent(left: &[Segment], right: &[Segment]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| match (left, right) {
                (Segment::Key(left), Segment::Key(right)) => left.eq_ignore_ascii_case(right),
                _ => left == right,
            })
}

/// Strip a leading `properties` wrapper; a standalone `properties` is a leaf.
pub fn without_properties(segments: &[Segment]) -> &[Segment] {
    if segments.len() > 1
        && matches!(segments.first(), Some(Segment::Key(key)) if key.eq_ignore_ascii_case("properties"))
    {
        segments.get(1..).unwrap_or_default()
    } else {
        segments
    }
}

/// Case-insensitive identity of a path, used by provenance records.
pub fn key(segments: &[Segment]) -> String {
    render(segments).to_ascii_lowercase()
}

pub fn render(segments: &[Segment]) -> String {
    let mut result = String::new();
    for segment in segments {
        match segment {
            Segment::Key(key) => {
                if !key.contains(['.', '[', ']', '\'', '"']) && key.trim() == key.as_ref() {
                    if !result.is_empty() {
                        result.push('.');
                    }
                    result.push_str(key);
                } else {
                    let quote = if key.match_indices('\'').any(|(offset, _)| {
                        key.get(offset.saturating_add(1)..)
                            .is_some_and(|tail| tail.trim_start().starts_with(']'))
                    }) {
                        '"'
                    } else {
                        '\''
                    };
                    result.push('[');
                    result.push(quote);
                    result.push_str(key);
                    result.push(quote);
                    result.push(']');
                }
            }
            Segment::Index(index) => result.push_str(&alloc::format!("[{index}]")),
            Segment::Wildcard => result.push_str("[*]"),
        }
    }
    result
}

/// Split only at actual wildcards, leaving quoted `[*]` untouched.
pub fn wildcard_parts(path: &str) -> Vec<&str> {
    let Some(parsed) = parse(path) else {
        return alloc::vec![path];
    };
    let mut parts = Vec::new();
    let mut start = 0;
    for (open, end) in parsed.wildcards {
        if let Some(part) = path.get(start..open) {
            parts.push(part);
        }
        start = if path.as_bytes().get(end) == Some(&b'.') {
            end.saturating_add(1)
        } else {
            end
        };
    }
    if let Some(part) = path.get(start..) {
        parts.push(part);
    }
    parts
}

pub fn get<'a>(
    mut value: &'a Value,
    segments: &[Segment],
    case_insensitive: bool,
) -> Option<&'a Value> {
    for segment in segments {
        value = match segment {
            Segment::Key(key) => {
                let object = value.as_object().ok()?;
                object.get(&Value::String(Rc::clone(key))).or_else(|| {
                    case_insensitive
                        .then(|| {
                            object.iter().find_map(|(candidate, child)| {
                                candidate
                                    .as_string()
                                    .ok()
                                    .filter(|s| s.eq_ignore_ascii_case(key))
                                    .map(|_| child)
                            })
                        })
                        .flatten()
                })?
            }
            Segment::Index(index) => value.as_array().ok()?.get(*index)?,
            Segment::Wildcard => return None,
        };
    }
    Some(value)
}

pub fn get_map<'a>(map: &'a ObjMap, segments: &[Segment]) -> Option<&'a Value> {
    let (Segment::Key(first), rest) = segments.split_first()? else {
        return None;
    };
    let value = map.get(first.as_ref()).or_else(|| {
        map.iter()
            .find_map(|(key, value)| key.eq_ignore_ascii_case(first).then_some(value))
    })?;
    get(value, rest, true)
}

fn map_key(map: &ObjMap, key: &str) -> Option<Rc<str>> {
    map.get_key_value(key)
        .map(|(actual, _)| actual)
        .or_else(|| {
            map.keys()
                .find(|candidate| candidate.eq_ignore_ascii_case(key))
        })
        .cloned()
}

fn object_key(object: &Object, key: &Rc<str>) -> Option<Value> {
    let exact = Value::String(Rc::clone(key));
    if object.contains_key(&exact) {
        return Some(exact);
    }
    object
        .keys()
        .find(|candidate| {
            candidate
                .as_string()
                .is_ok_and(|candidate| candidate.eq_ignore_ascii_case(key))
        })
        .cloned()
}

fn object_child<'a>(object: &'a Object, key: &Rc<str>) -> Option<&'a Value> {
    object.get(&Value::String(Rc::clone(key))).or_else(|| {
        object.iter().find_map(|(candidate, child)| {
            candidate
                .as_string()
                .is_ok_and(|candidate| candidate.eq_ignore_ascii_case(key))
                .then_some(child)
        })
    })
}

pub fn rename(map: &mut ObjMap, source: &str, target: &str, lowercase: bool) {
    let (Some(source), Some(target)) = (scalar_segments(source), scalar_segments(target)) else {
        return;
    };
    if equivalent(&source, &target) || get_map(map, &target).is_some() || !can_set(map, &target) {
        return;
    }
    if let Some(value) = get_map(map, &source).cloned() {
        remove(map, &source);
        set(map, &target, value, lowercase);
    }
}

fn empty_for(segment: &Segment) -> Value {
    if matches!(segment, Segment::Index(_)) {
        make_array(Vec::new())
    } else {
        make_value(new_map())
    }
}

fn key_case(key: &Rc<str>, lowercase: bool) -> Rc<str> {
    if lowercase && key.bytes().any(|byte| byte.is_ascii_uppercase()) {
        Rc::from(key.to_ascii_lowercase())
    } else {
        Rc::clone(key)
    }
}

pub fn set(map: &mut ObjMap, segments: &[Segment], value: Value, lowercase: bool) {
    if segments
        .iter()
        .any(|segment| matches!(segment, Segment::Index(index) if *index > MAX_INDEX))
    {
        return;
    }
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return;
    };
    let key = map_key(map, key).unwrap_or_else(|| key_case(key, lowercase));
    if let Some(next) = rest.first() {
        let child = map.entry(key).or_insert_with(|| empty_for(next));
        set_value(child, rest, value, lowercase);
    } else {
        map.insert(key, value);
    }
}

fn set_value(current: &mut Value, segments: &[Segment], value: Value, lowercase: bool) {
    let Some((segment, rest)) = segments.split_first() else {
        *current = value;
        return;
    };
    if matches!(current, Value::Null) {
        *current = empty_for(segment);
    }
    match (current, segment) {
        (Value::Object(object), Segment::Key(_)) => {
            set_object(Rc::make_mut(object), segments, value, lowercase);
        }
        (Value::Array(array), Segment::Index(index)) => {
            if *index > MAX_INDEX {
                return;
            }
            let array = Rc::make_mut(array);
            if *index >= array.len() {
                let Some(len) = index.checked_add(1) else {
                    return;
                };
                let mut values = array.to_vec();
                if values
                    .try_reserve(len.saturating_sub(values.len()))
                    .is_err()
                {
                    return;
                }
                values.resize(len, Value::Null);
                *array = values.into();
            }
            if let Some(child) = array.get_mut(*index) {
                if matches!(child, Value::Null) {
                    if let Some(next) = rest.first() {
                        *child = empty_for(next);
                    }
                }

                set_value(child, rest, value, lowercase);
            }
        }

        _ => {}
    }
}

pub fn set_object(object: &mut Object, segments: &[Segment], value: Value, lowercase: bool) {
    if segments
        .iter()
        .any(|segment| matches!(segment, Segment::Index(index) if *index > MAX_INDEX))
    {
        return;
    }
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return;
    };
    let key = object_key(object, key).unwrap_or_else(|| Value::String(key_case(key, lowercase)));
    if let Some(next) = rest.first() {
        let child = object.get_or_insert_with(key, || empty_for(next));
        set_value(child, rest, value, lowercase);
    } else {
        object.insert(key, value);
    }
}

/// Raw container shapes along alias short paths: array length, or `None`
/// for an object.
pub type Shapes = BTreeMap<String, Option<usize>>;

/// How removal treats containers it leaves empty.
pub enum Prune<'a> {
    /// Keep emptied containers.
    Never,
    /// Remove emptied objects and arrays left all-null.
    Empty,
    /// Remove only containers absent from `shapes`, and only trailing nulls
    /// past the raw array length or consumed during this pass.
    Tracked {
        shapes: &'a Shapes,
        consumed: &'a mut BTreeSet<String>,
    },
}

/// Record raw container shapes along `segments` before alias writes.
pub fn record_shapes(map: &ObjMap, segments: &[Segment], shapes: &mut Shapes) {
    let mut current = segments.get(..1).and_then(|first| get_map(map, first));
    for depth in 1..segments.len() {
        let Some(value) = current else {
            return;
        };
        let shape = match value {
            Value::Array(array) => Some(array.len()),
            Value::Object(_) => None,
            _ => return,
        };
        let (Some(prefix), Some(next)) = (segments.get(..depth), segments.get(depth..=depth))
        else {
            return;
        };
        shapes.insert(key(prefix), shape);
        current = get(value, next, true);
    }
}

/// Remove a consumed alias leaf without discarding unrelated siblings.
pub fn remove(map: &mut ObjMap, segments: &[Segment]) {
    remove_with(map, segments, &mut Prune::Empty);
}

pub fn remove_with(map: &mut ObjMap, segments: &[Segment], prune: &mut Prune<'_>) {
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return;
    };
    let Some(actual) = map_key(map, key) else {
        return;
    };
    let mut prefix = alloc::vec![Segment::Key(Rc::clone(&actual))];
    if rest.is_empty()
        || map
            .get_mut(&actual)
            .is_some_and(|value| remove_value(value, rest, &mut prefix, prune))
    {
        map.remove(&actual);
    }
}

fn remove_value(
    value: &mut Value,
    segments: &[Segment],
    prefix: &mut Vec<Segment>,
    prune: &mut Prune<'_>,
) -> bool {
    let Some((first, rest)) = segments.split_first() else {
        return false;
    };
    match (value, first) {
        (Value::Object(object), Segment::Key(_)) => {
            remove_in_object(Rc::make_mut(object), segments, prefix, prune)
        }
        (Value::Array(array), Segment::Index(index)) => {
            let array = Rc::make_mut(array);
            let Some(element) = array.get_mut(*index) else {
                return false;
            };
            prefix.push(Segment::Index(*index));
            let removed = rest.is_empty() || remove_value(element, rest, prefix, prune);
            if removed {
                *element = Value::Null;
                if let Prune::Tracked { consumed, .. } = prune {
                    consumed.insert(key(prefix));
                }
            }
            prefix.pop();
            if !removed {
                return false;
            }
            match prune {
                Prune::Never => false,
                Prune::Empty => array.iter().all(|item| matches!(item, Value::Null)),
                Prune::Tracked { shapes, consumed } => {
                    let raw = shapes.get(&key(prefix));
                    let raw_len = raw.copied().flatten().unwrap_or(0);
                    let mut values = array.to_vec();
                    while let Some(Value::Null) = values.last() {
                        let last = values.len().saturating_sub(1);
                        prefix.push(Segment::Index(last));
                        let removable = last >= raw_len || consumed.contains(&key(prefix));
                        prefix.pop();
                        if !removable {
                            break;
                        }
                        values.pop();
                    }
                    let empty = values.is_empty();
                    if values.len() != array.len() {
                        *array = values.into();
                    }
                    empty && raw.is_none()
                }
            }
        }
        _ => false,
    }
}

pub fn remove_object(object: &mut Object, segments: &[Segment], prune: bool) -> bool {
    let mut prune = if prune { Prune::Empty } else { Prune::Never };
    remove_in_object(object, segments, &mut Vec::new(), &mut prune)
}

fn remove_in_object(
    object: &mut Object,
    segments: &[Segment],
    prefix: &mut Vec<Segment>,
    prune: &mut Prune<'_>,
) -> bool {
    let Some((Segment::Key(key_name), rest)) = segments.split_first() else {
        return false;
    };
    let mut removed = false;
    if let Some(actual) = object_key(object, key_name) {
        prefix.push(Segment::Key(
            actual
                .as_string()
                .map_or_else(|_| Rc::clone(key_name), Rc::clone),
        ));
        if rest.is_empty()
            || object
                .get_mut(&actual)
                .is_some_and(|value| remove_value(value, rest, prefix, prune))
        {
            object.remove(&actual);
            removed = true;
        }
        prefix.pop();
    }
    match prune {
        Prune::Never => false,
        Prune::Empty => object.is_empty(),
        Prune::Tracked { shapes, .. } => {
            removed && object.is_empty() && !shapes.contains_key(&key(prefix))
        }
    }
}

/// Check shape compatibility before consuming the normalized source path.
pub fn can_set(map: &ObjMap, segments: &[Segment]) -> bool {
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return false;
    };
    let existing = map.get(key.as_ref()).or_else(|| {
        map.iter()
            .find_map(|(candidate, child)| candidate.eq_ignore_ascii_case(key).then_some(child))
    });
    can_set_value(existing, rest)
}

fn can_set_value(current: Option<&Value>, segments: &[Segment]) -> bool {
    let Some((segment, rest)) = segments.split_first() else {
        return true;
    };
    match (current, segment) {
        (_, Segment::Wildcard) => false,
        (_, Segment::Index(index)) if *index > MAX_INDEX => false,
        (None, _) | (Some(Value::Null), _) => can_set_value(None, rest),
        (Some(Value::Object(object)), Segment::Key(key)) => {
            can_set_value(object_child(object, key), rest)
        }
        (Some(Value::Array(array)), Segment::Index(index)) => {
            can_set_value(array.get(*index), rest)
        }
        _ => false,
    }
}
