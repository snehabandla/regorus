// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Shared classification for Azure Policy tag field paths.

use alloc::string::String;

#[derive(Debug, PartialEq, Eq)]
pub enum TagField {
    Collection,
    Key(String),
    Wildcard,
    Empty,
}

pub struct BracketTag<'a> {
    pub name: &'a str,
    pub quoted: bool,
}

pub fn normalize_bracket_tag(contents: &str) -> BracketTag<'_> {
    let trimmed = contents.trim();
    strip_matching_outer_quotes(trimmed).map_or(
        BracketTag {
            name: trimmed,
            quoted: false,
        },
        |name| BracketTag { name, quoted: true },
    )
}

/// Classify a field path that may name the tag collection or one tag.
///
/// Bracket names are trimmed using Unicode whitespace rules and have one
/// matching pair of outer quotes removed. Whitespace inside quotes remains
/// part of the tag name. Wildcard spellings are left for the caller to handle
/// according to its context.
pub fn classify_tag_field(text: &str) -> Option<TagField> {
    let lower = text.to_lowercase();

    match lower.as_str() {
        "tags" => Some(TagField::Collection),
        _ if lower.starts_with("tags.") => {
            let tag = text.get("tags.".len()..).unwrap_or_default();
            if tag.is_empty() {
                Some(TagField::Empty)
            } else {
                Some(TagField::Key(tag.into()))
            }
        }
        _ if lower.starts_with("tags[") && text.ends_with(']') => {
            let contents = text
                .get("tags[".len()..text.len().saturating_sub(1))
                .unwrap_or_default();
            let bracket_tag = normalize_bracket_tag(contents);
            let tag = bracket_tag.name;

            if tag.is_empty() {
                Some(TagField::Empty)
            } else if bracket_tag.quoted {
                Some(TagField::Key(tag.into()))
            } else if text.contains("[*]") {
                Some(TagField::Wildcard)
            } else {
                Some(TagField::Key(tag.into()))
            }
        }
        _ => None,
    }
}

fn strip_matching_outer_quotes(s: &str) -> Option<&str> {
    s.strip_prefix('\'')
        .and_then(|inner| inner.strip_suffix('\''))
        .or_else(|| {
            s.strip_prefix('"')
                .and_then(|inner| inner.strip_suffix('"'))
        })
}
