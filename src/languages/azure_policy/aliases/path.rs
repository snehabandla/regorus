// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Alias-local path grammar. Quotes have no escapes and close only before
//! optional whitespace and `]`; delimiters inside quoted keys are literal.

use alloc::vec::Vec;

use crate::{value::Object, Rc, Value};

use super::obj_map::{make_array, make_value, new_map, ObjMap};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Segment {
    Key(Rc<str>),
    Index(usize),
    Wildcard,
}

pub(crate) struct Path {
    pub segments: Vec<Segment>,
    wildcards: Vec<(usize, usize)>,
}

pub(crate) fn parse(path: &str) -> Option<Path> {
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
            None => return Some(Path { segments, wildcards }),
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
        Segment::Index(key.parse().unwrap_or(usize::MAX))
    } else {
        Segment::Key(Rc::from(key))
    };
    Some((segment, body_start.saturating_add(close).saturating_add(1)))
}

pub(crate) fn scalar_segments(path: &str) -> Option<Vec<Segment>> {
    let parsed = parse(path)?;
    parsed.wildcards.is_empty().then_some(parsed.segments)
}

/// Split only at actual wildcards, leaving quoted `[*]` untouched.
pub(crate) fn wildcard_parts(path: &str) -> Vec<&str> {
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

pub(crate) fn get<'a>(
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
                            object.iter().find_map(|(candidate, value)| {
                                candidate
                                    .as_string()
                                    .ok()
                                    .filter(|s| s.eq_ignore_ascii_case(key))
                                    .map(|_| value)
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

pub(crate) fn set(map: &mut ObjMap, segments: &[Segment], value: Value, lowercase: bool) {
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return;
    };
    let key = key_case(key, lowercase);
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
    match (current, segment) {
        (Value::Object(object), Segment::Key(_)) => set_object(Rc::make_mut(object), segments, value, lowercase),
        (Value::Array(array), Segment::Index(index)) => {
            let array = Rc::make_mut(array);
            if *index >= array.len() {
                let Some(len) = index.checked_add(1) else {
                    return;
                };
                if array.try_reserve(len.saturating_sub(array.len())).is_err() {
                    return;
                }
                array.resize(len, Value::Null);
            }
            if let Some(child) = array.get_mut(*index) {
                if matches!(child, Value::Null) {
                    if let Some(next) = rest.first() {
                        *child = empty_for(next);
                    }
                }

                pub(crate) fn set_object(object: &mut Object, segments: &[Segment], value: Value, lowercase: bool) {
                    let Some((Segment::Key(key), rest)) = segments.split_first() else {
                        return;
                    };
                    let key = Value::String(key_case(key, lowercase));
                    if let Some(next) = rest.first() {
                        let child = object.get_or_insert_with(key, || empty_for(next));
                        set_value(child, rest, value, lowercase);
                    } else {
                        object.insert(key, value);
                    }
                }

                /// Remove a consumed alias leaf without discarding unrelated siblings.
                pub(crate) fn remove(map: &mut ObjMap, segments: &[Segment]) {
                    let Some((Segment::Key(key), rest)) = segments.split_first() else {
                        return;
                    };
                    let Some(actual) = map.keys().find(|candidate| candidate.eq_ignore_ascii_case(key)).cloned() else {
                        return;
                    };
                    if rest.is_empty() || map.get_mut(&actual).is_some_and(|value| remove_value(value, rest)) {
                        map.remove(&actual);
                    }
                }

                fn remove_value(value: &mut Value, segments: &[Segment]) -> bool {
                    let Some((first, rest)) = segments.split_first() else {
                        return false;
                    };
                    match (value, first) {
                        (Value::Object(object), Segment::Key(key)) => {
                            let object = Rc::make_mut(object);
                            let actual = object.keys().find(|candidate| {
                                candidate.as_string().is_ok_and(|candidate| candidate.eq_ignore_ascii_case(key))
                            }).cloned();
                            if let Some(actual) = actual {
                                if rest.is_empty() || object.get_mut(&actual).is_some_and(|value| remove_value(value, rest)) {
                                    object.remove(&actual);
                                }
                            }
                            object.is_empty()
                        }
                        (Value::Array(array), Segment::Index(index)) => {
                            if let Some(value) = Rc::make_mut(array).get_mut(*index) {
                                if rest.is_empty() || remove_value(value, rest) {
                                    *value = Value::Null;
                                }
                            }
                            false
                        }
                        _ => false,
                    }
                }
                set_value(child, rest, value, lowercase);
            }
        }
        _ => {}
    }
}
