// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Alias-local path grammar. Quotes have no escapes and close only before
//! optional whitespace and `]`; delimiters inside quoted keys are literal.

use alloc::vec::Vec;
use alloc::string::String;

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
    left.len() == right.len() && left.iter().zip(right).all(|(left, right)| match (left, right) {
        (Segment::Key(left), Segment::Key(right)) => left.eq_ignore_ascii_case(right),
        _ => left == right,
    })
}

pub fn without_properties(segments: &[Segment]) -> &[Segment] {
    if matches!(segments.first(), Some(Segment::Key(key)) if key.eq_ignore_ascii_case("properties")) {
        segments.get(1..).unwrap_or_default()
    } else {
        segments
    }
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
                        key.get(offset.saturating_add(1)..).is_some_and(|tail| tail.trim_start().starts_with(']'))
                    }) { '"' } else { '\'' };
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
    let value = map.iter().find_map(|(key, value)| key.eq_ignore_ascii_case(first).then_some(value))?;
    get(value, rest, true)
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
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return;
    };
    let key = map.keys().find(|candidate| candidate.eq_ignore_ascii_case(key))
        .cloned().unwrap_or_else(|| key_case(key, lowercase));
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
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return;
    };
    let key = object.keys().find(|candidate| candidate.as_string()
        .is_ok_and(|candidate| candidate.eq_ignore_ascii_case(key))).cloned()
        .unwrap_or_else(|| Value::String(key_case(key, lowercase)));
    if let Some(next) = rest.first() {
        let child = object.get_or_insert_with(key, || empty_for(next));
        set_value(child, rest, value, lowercase);
    } else {
        object.insert(key, value);
    }
}

/// Remove a consumed alias leaf without discarding unrelated siblings.
pub fn remove(map: &mut ObjMap, segments: &[Segment]) {
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return;
    };
    let Some(actual) = map
        .keys()
        .find(|candidate| candidate.eq_ignore_ascii_case(key))
        .cloned()
    else {
        return;
    };
    if rest.is_empty()
        || map
            .get_mut(&actual)
            .is_some_and(|value| remove_value(value, rest, true))
    {
        map.remove(&actual);
    }
}

fn remove_value(value: &mut Value, segments: &[Segment], prune: bool) -> bool {
    let Some((first, rest)) = segments.split_first() else {
        return false;
    };
    match (value, first) {
        (Value::Object(object), Segment::Key(_)) => {
            remove_object(Rc::make_mut(object), segments, prune)
        }
        (Value::Array(array), Segment::Index(index)) => {
            let mut consumed = false;
            if let Some(child) = Rc::make_mut(array).get_mut(*index) {
                if rest.is_empty() || remove_value(child, rest, prune) {
                    *child = Value::Null;
                    consumed = true;
                }
            }
            prune && consumed && array.iter().all(|child| matches!(child, Value::Null))
        }
        _ => false,
    }
}

pub fn remove_object(object: &mut Object, segments: &[Segment], prune: bool) -> bool {
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return false;
    };
    let actual = object
        .keys()
        .find(|candidate| {
            candidate
                .as_string()
                .is_ok_and(|candidate| candidate.eq_ignore_ascii_case(key))
        })
        .cloned();
    if let Some(actual) = actual {
        if rest.is_empty()
            || object
                .get_mut(&actual)
                .is_some_and(|value| remove_value(value, rest, prune))
        {
            object.remove(&actual);
        }

        /// Check shape compatibility before consuming the normalized source path.
        pub fn can_set(map: &ObjMap, segments: &[Segment]) -> bool {
            let Some((Segment::Key(key), rest)) = segments.split_first() else {
                return false;
            };
            let existing = map.iter().find_map(|(candidate, child)| candidate.eq_ignore_ascii_case(key).then_some(child));
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
                    let child = object.iter().find_map(|(candidate, child)| candidate.as_string()
                        .is_ok_and(|candidate| candidate.eq_ignore_ascii_case(key)).then_some(child));
                    can_set_value(child, rest)
                }
                (Some(Value::Array(array)), Segment::Index(index)) => can_set_value(array.get(*index), rest),
                _ => false,
            }
        }
    }
    prune && object.is_empty()
}
