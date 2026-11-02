// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Alias-local path grammar. Quotes have no escapes and close only before
//! optional whitespace and `]`; delimiters inside quoted keys are literal.
//!
//! Unquoted brackets follow the policy compiler's field paths: only the exact
//! text `[*]` is a wildcard (`[ * ]` is the key `*`), trimmed digits are an
//! index (`[ 0 ]`), and a dot before a bracket is accepted (`a.[0]`). Paths
//! longer than [`MAX_SEGMENTS`] are rejected.

use alloc::string::String;
use alloc::vec::Vec;

use crate::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Segment {
    Key(Rc<str>),
    Index(usize),
    Wildcard,
}

/// Largest accepted array index, bounding sparse arrays built from catalog paths.
pub const MAX_INDEX: usize = 4095;

/// Bound path depth so hostile catalogs cannot drive deep recursion.
pub const MAX_SEGMENTS: usize = 64;

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
        if segments.len() > MAX_SEGMENTS {
            return None;
        }
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
