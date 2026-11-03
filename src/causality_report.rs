// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]

//! Materialization of causality reports from static metadata + runtime trace.
//!
//! This module combines the compile-time `StaticConditionInfo` from
//! [`crate::static_provenance`] with the runtime [`crate::evaluation_trace::EvaluationTrace`]
//! to produce the final [`CausalityReport`] JSON output.

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use serde::Serialize;

use crate::evaluation_trace::{
    AssumptionKind, ConditionMode, ConditionOutcome, EvaluationTrace, ExplanationDetail,
    ExplanationScope, ExplanationSettings, RuleOutcome, ValueMode,
};
use crate::rvm::program::{Program, RuleType};
use crate::rvm::Instruction;
use crate::static_provenance::{Provenance, ProvenanceRoot};
use crate::value::Value;

// ---------------------------------------------------------------------------
// Redaction
// ---------------------------------------------------------------------------

/// Name fragments that mark a field as sensitive when value_mode is Redacted.
/// Matched against names normalized by `normalize_name`, so `api_key`,
/// `api-key` and `apiKey` all match `apikey`.
const SENSITIVE_FIELDS: &[&str] = &[
    "password",
    "passwd",
    "pwd",
    "passphrase",
    "secret",
    "token",
    "apikey",
    "jwt",
    "credential",
    "privatekey",
    "accesskey",
    "connectionstring",
    "securevalue",
    "protectedsettings",
];

/// Key-material names, matched only at the end of a normalized name so that
/// settings about a key (`allowSharedKeyAccess`) are not mistaken for one.
const SENSITIVE_KEY_SUFFIXES: &[&str] = &[
    "accountkey",
    "sharedkey",
    "primarykey",
    "secondarykey",
    "subscriptionkey",
];

fn should_redact_path(provenance: Option<&Provenance>) -> bool {
    let Some(prov) = provenance else {
        return false;
    };
    for seg in &prov.segments {
        if let crate::static_provenance::Segment::Field(ref name) = *seg {
            if is_sensitive_name(name) {
                return true;
            }
        }
    }
    false
}

/// Bytes of `name`, ASCII-lowercased, without the separators `-`, `_` and space.
fn normalized_name_bytes(name: &str) -> impl Iterator<Item = u8> + '_ {
    name.bytes()
        .filter(|b| !matches!(*b, b'-' | b'_' | b' '))
        .map(|b| b.to_ascii_lowercase())
}

/// Names up to this many normalized bytes are checked without allocating;
/// every sensitive fragment is far shorter.
const INLINE_NAME_BYTES: usize = 64;

/// Whether `name` is sensitive: after normalization it contains a
/// `SENSITIVE_FIELDS` fragment or ends with a `SENSITIVE_KEY_SUFFIXES` one.
///
/// Runs for every object key of every value a `Redacted` report walks, so the
/// common short name is normalized into a stack buffer rather than a `String`.
fn is_sensitive_name(name: &str) -> bool {
    let mut inline = [0_u8; INLINE_NAME_BYTES];
    let mut len = 0_usize;
    for byte in normalized_name_bytes(name) {
        let Some(slot) = inline.get_mut(len) else {
            let heap: Vec<u8> = normalized_name_bytes(name).collect();
            return is_sensitive_normalized(&heap);
        };
        *slot = byte;
        len = len.saturating_add(1);
    }
    is_sensitive_normalized(inline.get(..len).unwrap_or_default())
}

fn is_sensitive_normalized(name: &[u8]) -> bool {
    SENSITIVE_FIELDS.iter().any(|fragment| {
        name.windows(fragment.len())
            .any(|window| window == fragment.as_bytes())
    }) || SENSITIVE_KEY_SUFFIXES
        .iter()
        .any(|suffix| name.ends_with(suffix.as_bytes()))
}

/// Whether `map` is a name/value pair whose `name` is sensitive, as in ARM
/// `appSettings` or container `env` entries (`{"name": "DB_PASSWORD",
/// "value": "..."}`); its `value` entry is then sensitive too.
pub(crate) fn is_sensitive_pair(map: &crate::value::Object) -> bool {
    map.get(&Value::from("name"))
        .and_then(|name| name.as_string().ok())
        .is_some_and(|name| is_sensitive_name(name))
}

/// Whether an object entry under `key` holds a sensitive value;
/// `pair_sensitive` is `is_sensitive_pair` of the enclosing object.
fn is_sensitive_entry(key: &Value, pair_sensitive: bool) -> bool {
    key.as_string()
        .is_ok_and(|k| is_sensitive_name(k) || (pair_sensitive && k.as_ref() == "value"))
}

/// Nesting beyond this depth is treated as sensitive rather than walked.
const MAX_REDACT_DEPTH: usize = 64;

/// Whether `value` holds a sensitive-named object key at any depth, in object
/// values or in compound (non-string) object keys. Fails closed past the depth cap.
fn contains_nested_secret(value: &Value, depth: usize) -> bool {
    if !matches!(*value, Value::Object(_) | Value::Array(_) | Value::Set(_)) {
        return false;
    }
    if depth >= MAX_REDACT_DEPTH {
        return true;
    }
    let next = depth.saturating_add(1);
    match *value {
        Value::Object(ref map) => {
            // One pass: a sensitive key, a nested secret, or a name/value pair
            // whose `name` is sensitive (see `is_sensitive_pair`).
            let mut sensitive_name_entry = false;
            let mut has_value_entry = false;
            for (key, item) in map.iter() {
                if let Ok(key_name) = key.as_string() {
                    if is_sensitive_name(key_name) {
                        return true;
                    }
                    match key_name.as_ref() {
                        "name" => {
                            sensitive_name_entry =
                                item.as_string().is_ok_and(|name| is_sensitive_name(name));
                        }
                        "value" => has_value_entry = true,
                        _ => {}
                    }
                }
                if contains_nested_secret(key, next) || contains_nested_secret(item, next) {
                    return true;
                }
            }
            sensitive_name_entry && has_value_entry
        }
        Value::Array(ref items) => items.iter().any(|item| contains_nested_secret(item, next)),
        Value::Set(ref items) => items.iter().any(|item| contains_nested_secret(item, next)),
        _ => false,
    }
}

/// Replace values under sensitive-named object keys anywhere inside `value`.
///
/// Returns `None` when nothing needed redacting, without copying. Path-based
/// redaction only sees the operand's own path; a harmlessly named object
/// (`input.profile`) can still nest `password`. A secret inside a compound
/// object key cannot be rewritten without colliding keys, so the whole
/// enclosing object is redacted instead.
fn redact_nested_secrets(value: &Value, depth: usize) -> Option<Value> {
    if !contains_nested_secret(value, depth) {
        return None;
    }
    if depth >= MAX_REDACT_DEPTH {
        return Some(Value::from("<redacted>"));
    }
    let next = depth.saturating_add(1);
    let redact_items =
        |item: &Value| redact_nested_secrets(item, next).unwrap_or_else(|| item.clone());
    Some(match *value {
        Value::Object(ref map) => {
            if map.keys().any(|key| contains_nested_secret(key, next)) {
                return Some(Value::from("<redacted>"));
            }
            let pair_sensitive = is_sensitive_pair(map);
            let out: alloc::collections::BTreeMap<Value, Value> = map
                .iter()
                .map(|(key, item)| {
                    let replaced = if is_sensitive_entry(key, pair_sensitive) {
                        Value::from("<redacted>")
                    } else {
                        redact_items(item)
                    };
                    (key.clone(), replaced)
                })
                .collect();
            Value::from(out)
        }
        Value::Array(ref items) => Value::from(items.iter().map(redact_items).collect::<Vec<_>>()),
        Value::Set(ref items) => Value::from(
            items
                .iter()
                .map(redact_items)
                .collect::<alloc::collections::BTreeSet<_>>(),
        ),
        _ => return None,
    })
}

/// Element budget for one two-operand condition operand, counted across all
/// nesting levels so nested collections cannot multiply it.
const MAX_OPERAND_ELEMENTS: usize = 100;

/// Spend one element of `budget`; `false` once it is exhausted.
const fn consume_element(budget: &mut usize) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget = budget.saturating_sub(1);
    true
}

/// Whether every element of `value`, at every depth, fits in `budget`.
/// Recursion depth is bounded by the budget itself.
fn fits_element_budget(value: &Value, budget: &mut usize) -> bool {
    match *value {
        Value::Array(ref items) => items
            .iter()
            .all(|item| consume_element(budget) && fits_element_budget(item, budget)),
        Value::Set(ref items) => items
            .iter()
            .all(|item| consume_element(budget) && fits_element_budget(item, budget)),
        Value::Object(ref map) => map.iter().all(|(key, item)| {
            consume_element(budget)
                && fits_element_budget(key, budget)
                && fits_element_budget(item, budget)
        }),
        _ => true,
    }
}

/// Copy `value`, keeping elements in iteration order until `budget` runs out.
fn take_within_element_budget(value: &Value, budget: &mut usize) -> Value {
    match *value {
        Value::Array(ref items) => {
            let mut out = Vec::new();
            for item in items.iter() {
                if !consume_element(budget) {
                    break;
                }
                out.push(take_within_element_budget(item, budget));
            }
            Value::from(out)
        }
        Value::Set(ref items) => {
            let mut out = alloc::collections::BTreeSet::new();
            for item in items.iter() {
                if !consume_element(budget) {
                    break;
                }
                out.insert(take_within_element_budget(item, budget));
            }
            Value::from(out)
        }
        Value::Object(ref map) => {
            let mut out = alloc::collections::BTreeMap::new();
            for (key, item) in map.iter() {
                if !consume_element(budget) {
                    break;
                }
                // Keys are kept whole to preserve identity; stop before an
                // entry whose compound key would not fit the remaining budget.
                let mut after_key = *budget;
                if !fits_element_budget(key, &mut after_key) {
                    break;
                }
                *budget = after_key;
                out.insert(key.clone(), take_within_element_budget(item, budget));
            }
            Value::from(out)
        }
        _ => value.clone(),
    }
}

/// Cut an oversized collection operand to `MAX_OPERAND_ELEMENTS`.
///
/// Returns the kept prefix and the original top-level element count, or `None`
/// when the operand already fits (the common case, with no copy).
fn truncate_operand(value: &Value) -> Option<(Value, usize)> {
    let length = match *value {
        Value::Array(ref items) => items.len(),
        Value::Set(ref items) => items.len(),
        Value::Object(ref map) => map.len(),
        _ => return None,
    };
    let mut probe = MAX_OPERAND_ELEMENTS;
    if fits_element_budget(value, &mut probe) {
        return None;
    }
    let mut budget = MAX_OPERAND_ELEMENTS;
    Some((take_within_element_budget(value, &mut budget), length))
}

/// One segment of a runtime provenance path.
#[derive(Debug, PartialEq, Eq)]
struct PathSegment<'a> {
    /// Byte offset just past the segment in the path text.
    end: usize,
    /// The segment's key when it names an object field (the root, `.ident`
    /// or `["string"]`); `None` for an index or any other bracketed value.
    /// Borrowed from the path unless a quoted key holds escapes.
    key: Option<alloc::borrow::Cow<'a, str>>,
}

/// Segments of a runtime provenance path in the grammar the VM writes:
/// `root(.ident | ["json string"] | [other])*`. Yields `Err(())` once, and
/// then stops, where the text does not follow it. Does not allocate unless a
/// quoted key holds escapes.
struct RuntimePathSegments<'a> {
    path: &'a str,
    pos: usize,
    done: bool,
}

impl<'a> RuntimePathSegments<'a> {
    const fn new(path: &'a str) -> Self {
        Self {
            path,
            pos: 0,
            done: false,
        }
    }

    fn next_segment(&mut self) -> Option<PathSegment<'a>> {
        use alloc::borrow::Cow;
        let path = self.path;
        let bytes = path.as_bytes();
        let is_ident = |b: u8| b == b'_' || b.is_ascii_alphanumeric();
        let ident_len = |from: usize| {
            bytes
                .get(from..)
                .map_or(0, |rest| rest.iter().take_while(|&&b| is_ident(b)).count())
        };
        if self.pos == 0 {
            let len = ident_len(0);
            if len == 0 {
                return None;
            }
            self.pos = len;
            return Some(PathSegment {
                end: len,
                key: Some(Cow::Borrowed(path.get(..len)?)),
            });
        }
        match bytes.get(self.pos).copied()? {
            b'.' => {
                // `IndexLiteral` writes any string key after a dot, so a field
                // runs to the next `.` or `[`.
                let start = self.pos.saturating_add(1);
                let len = bytes.get(start..).map_or(0, |rest| {
                    rest.iter().take_while(|&&b| b != b'.' && b != b'[').count()
                });
                if len == 0 {
                    return None;
                }
                self.pos = start.saturating_add(len);
                Some(PathSegment {
                    end: self.pos,
                    key: Some(Cow::Borrowed(path.get(start..self.pos)?)),
                })
            }
            b'[' => {
                let start = self.pos.saturating_add(1);
                let (close, key) = if bytes.get(start) == Some(&b'"') {
                    let close = closing_quote(bytes, start.saturating_add(1))?;
                    let inner = path.get(start.saturating_add(1)..close)?;
                    let key = if inner.contains('\\') {
                        Cow::Owned(serde_json::from_str::<String>(path.get(start..=close)?).ok()?)
                    } else {
                        Cow::Borrowed(inner)
                    };
                    (close.saturating_add(1), Some(key))
                } else {
                    let close = closing_bracket(bytes, start)?;
                    let inner = path.get(start..close)?;
                    // A number is an index; anything else is a compound key.
                    let is_index = inner.parse::<f64>().is_ok();
                    (close, (!is_index).then_some(Cow::Borrowed(inner)))
                };
                if bytes.get(close) != Some(&b']') {
                    return None;
                }
                self.pos = close.saturating_add(1);
                Some(PathSegment { end: self.pos, key })
            }
            _ => None,
        }
    }
}

impl<'a> Iterator for RuntimePathSegments<'a> {
    type Item = Result<PathSegment<'a>, ()>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done || (self.pos > 0 && self.pos >= self.path.len()) {
            return None;
        }
        let segment = self.next_segment();
        if segment.is_none() {
            self.done = true;
        }
        Some(segment.ok_or(()))
    }
}

/// All segments of a runtime path, or `None` when it does not parse.
fn parse_runtime_path(path: &str) -> Option<Vec<PathSegment<'_>>> {
    RuntimePathSegments::new(path)
        .collect::<Result<_, _>>()
        .ok()
}

/// Index of the `"` closing a JSON string whose content starts at `from`.
fn closing_quote(bytes: &[u8], from: usize) -> Option<usize> {
    let mut escaped = false;
    for (offset, &b) in bytes.get(from..)?.iter().enumerate() {
        match b {
            _ if escaped => escaped = false,
            b'\\' => escaped = true,
            b'"' => return Some(from.saturating_add(offset)),
            _ => {}
        }
    }
    None
}

/// Index of the `]` closing a bracket whose content starts at `from`, skipping
/// nested brackets, braces and strings (a compound key's display).
fn closing_bracket(bytes: &[u8], from: usize) -> Option<usize> {
    let mut depth = 0_usize;
    let mut pos = from;
    while let Some(&b) = bytes.get(pos) {
        match b {
            b'"' => pos = closing_quote(bytes, pos.saturating_add(1))?,
            b'[' | b'{' => depth = depth.saturating_add(1),
            b']' if depth == 0 => return Some(pos),
            b']' | b'}' => depth = depth.checked_sub(1)?,
            _ => {}
        }
        pos = pos.saturating_add(1);
    }
    None
}

/// Index of the first segment at which a runtime path becomes sensitive: a
/// sensitive-named key, or the end of a recorded sensitive pair value (see
/// `EvaluationTrace::sensitive_value_paths`). A path that does not parse is
/// sensitive at its root if any part of it looks sensitive.
fn sensitive_segment(path: &str, trace: &EvaluationTrace) -> Option<usize> {
    let check_pairs = !trace.sensitive_value_paths.is_empty();
    for (index, segment) in RuntimePathSegments::new(path).enumerate() {
        let Ok(segment) = segment else {
            let pair_prefix = trace.sensitive_value_paths.iter().any(|recorded| {
                path.strip_prefix(recorded.as_str())
                    .is_some_and(|rest| rest.is_empty() || rest.starts_with(['.', '[']))
            });
            let named = path
                .split(['.', '[', ']', '"'])
                .any(|part| !part.is_empty() && is_sensitive_name(part));
            // Past the record's cap, an unreadable path may hide a pair value.
            return (pair_prefix || named || trace.sensitive_value_paths_overflowed).then_some(0);
        };
        let key_sensitive = segment.key.as_deref().is_some_and(|key| {
            is_sensitive_name(key) || (trace.sensitive_value_paths_overflowed && key == "value")
        });
        let pair_value = check_pairs
            && path
                .get(..segment.end)
                .is_some_and(|prefix| trace.sensitive_value_paths.contains(prefix));
        if key_sensitive || pair_value {
            return Some(index);
        }
    }
    None
}

/// Whether `value` is a key of a sensitive collection (see
/// `EvaluationTrace::sensitive_keys`). `has_path` tells whether the value has
/// a runtime path of its own, which a key never does.
fn is_sensitive_key(value: &Value, has_path: bool, trace: &EvaluationTrace) -> bool {
    matches!(*value, Value::String(_))
        && (trace.sensitive_keys.contains(value) || (trace.sensitive_keys_overflowed && !has_path))
}

/// Whether a runtime path reaches sensitive data (see `sensitive_segment`).
pub(crate) fn should_redact_runtime_path(path: Option<&str>, trace: &EvaluationTrace) -> bool {
    path.is_some_and(|path| sensitive_segment(path, trace).is_some())
}

/// Hide the keys a runtime path reveals beneath its first sensitive segment
/// (the keys of a secret collection are themselves secret): each later field
/// key becomes `["<redacted>"]`; indices are kept. Returns `None` when nothing
/// changes. An unparsable sensitive path is hidden whole.
fn mask_runtime_path(path: &str, trace: &EvaluationTrace) -> Option<String> {
    mask_runtime_path_from(path, sensitive_segment(path, trace)?)
}

/// `mask_runtime_path` once the first sensitive segment is known.
fn mask_runtime_path_from(path: &str, first: usize) -> Option<String> {
    let Some(segments) = parse_runtime_path(path) else {
        return Some(String::from("<redacted>"));
    };
    let mut start = segments.get(first)?.end;
    let mut masked = String::from(path.get(..start)?);
    let mut changed = false;
    for segment in segments.get(first.saturating_add(1)..)? {
        if segment.key.is_some() {
            masked.push_str("[\"<redacted>\"]");
            changed = true;
        } else {
            masked.push_str(path.get(start..segment.end)?);
        }
        start = segment.end;
    }
    changed.then_some(masked)
}

/// `redact_nested_secrets(value, 0)`, remembered per collection allocation.
///
/// A report shows the same shared collection (a whole resource bound by
/// `some r in input.resources`) in many conditions; the walk depends only on
/// the value, so it is done once per allocation for the life of the trace.
fn redact_nested_secrets_cached(value: &Value, trace: &EvaluationTrace) -> Option<Value> {
    let address = match *value {
        Value::Object(ref map) => crate::Rc::as_ptr(map).cast::<u8>().addr(),
        Value::Array(ref items) => crate::Rc::as_ptr(items).cast::<u8>().addr(),
        Value::Set(ref items) => crate::Rc::as_ptr(items).cast::<u8>().addr(),
        _ => return None,
    };
    if let Ok(cache) = trace.nested_secret_cache.try_borrow() {
        if let Some((_, result)) = cache.get(&address) {
            return result.clone();
        }
    }
    let result = redact_nested_secrets(value, 0);
    if let Ok(mut cache) = trace.nested_secret_cache.try_borrow_mut() {
        cache.insert(address, (value.clone(), result.clone()));
    }
    result
}

/// Sanitize a value for a `Redacted` report: the whole value when `sensitive`,
/// otherwise only secrets nested inside it.
fn sanitize_value(value: &Value, sensitive: bool, trace: &EvaluationTrace) -> Option<Value> {
    if sensitive {
        Some(Value::from("<redacted>"))
    } else {
        redact_nested_secrets_cached(value, trace)
    }
}

/// Whether `rule_name` is a result the caller queried (an entry point or a
/// rule under an entry-point package) rather than a helper it did not ask for.
fn is_output_rule(rule_name: &str, program: &Program) -> bool {
    program.entry_points.keys().any(|entry| {
        rule_name == entry
            || rule_name
                .strip_prefix(entry.as_str())
                .is_some_and(|rest| rest.starts_with('.'))
    })
}

fn assumed_input_path_for_pc(trace: &EvaluationTrace, pc: u32) -> Option<String> {
    trace
        .assumptions
        .iter()
        .find(|assumption| assumption.pc == pc)
        .map(|assumption| assumption.input_path.clone())
}

fn operand_provenance_for_output(
    runtime_path: Option<&str>,
    static_provenance: Option<&Provenance>,
    outcome: &ConditionOutcome,
    trace: &EvaluationTrace,
) -> Option<String> {
    if let Some(path) = runtime_path {
        return Some(path.to_string());
    }

    if outcome.assumed
        && matches!(
            static_provenance.map(|provenance| &provenance.root),
            Some(ProvenanceRoot::RuleResult { .. })
        )
    {
        if let Some(path) = assumed_input_path_for_pc(trace, outcome.pc) {
            return Some(path);
        }
    }

    static_provenance.map(|provenance| provenance.to_string())
}

// ---------------------------------------------------------------------------
// Output types
// ---------------------------------------------------------------------------

/// Top-level causality report.
#[derive(Debug, Clone, Serialize)]
pub struct CausalityReport {
    /// The value returned by the evaluated query.
    pub query_result: Value,
    /// Per-rule explanation details.
    pub rules: Vec<RuleExplanation>,
    /// Assumptions made when unknown input handling was active.
    pub assumptions: Vec<AssumptionRecord>,
}

/// Explanation for a single rule.
#[derive(Debug, Clone, Serialize)]
pub struct RuleExplanation {
    /// Fully-qualified rule name, e.g. `"data.test.allow"`.
    pub name: String,
    /// Rule type.
    #[serde(rename = "type")]
    pub rule_type: String,
    /// Final result of the rule.
    pub result: Value,
    /// Per-emission explanations for partial-set rules.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub emissions: Vec<EmissionExplanation>,
    /// Explanations for each definition that was evaluated.
    pub definitions: Vec<DefinitionExplanation>,
    /// `true` when `result` was rewritten by redaction.
    #[serde(default, skip_serializing_if = "is_false")]
    pub redacted: bool,
}

/// Explanation for a single emitted partial-set value.
#[derive(Debug, Clone, Serialize)]
pub struct EmissionExplanation {
    /// Stable 0-based index of this materialized emission within the rule.
    pub index: usize,
    /// Definition that produced this value.
    pub definition_index: u16,
    /// The emitted value.
    pub result: Value,
    /// Conditions active when the value was emitted.
    pub conditions: Vec<ConditionExplanation>,
    /// Every distinct derivation of `result`, in trace order and including the
    /// first, whose `definition_index` and `conditions` the top-level fields
    /// repeat. Present only when `ExplanationSettings::max_derivations` is
    /// greater than one; holds at most that many entries.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub derivations: Vec<DerivationExplanation>,
    /// Number of distinct derivations found for `result`. Present only with
    /// `derivations_truncated`. Approximate when the list is incomplete
    /// (value capture exhausted, or a derivation could not be fingerprinted).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub derivation_count: Option<usize>,
    /// `true` when `derivations` was cut to `max_derivations`, or when the
    /// list may be incomplete.
    #[serde(default, skip_serializing_if = "is_false")]
    pub derivations_truncated: bool,
    /// `true` when `result` was rewritten by redaction.
    #[serde(default, skip_serializing_if = "is_false")]
    pub redacted: bool,
}

/// One derivation of an emitted partial-set value: the definition that
/// produced it and the conditions active when it was emitted. Two derivations
/// are distinct unless both the definition and every condition are equal.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct DerivationExplanation {
    /// Definition that produced this derivation.
    pub definition_index: u16,
    /// Conditions active when this derivation emitted the value.
    pub conditions: Vec<ConditionExplanation>,
}

/// Explanation for a single rule definition body.
#[derive(Debug, Clone, Serialize)]
pub struct DefinitionExplanation {
    /// 0-based definition index within the rule.
    pub index: u16,
    /// Whether this definition succeeded or failed.
    pub outcome: String,
    /// Source location of the definition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// Condition evaluations within this definition.
    pub conditions: Vec<ConditionExplanation>,
}

/// A single condition evaluation.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ConditionExplanation {
    /// Source text of the condition.
    pub text: String,
    /// `"success"`, `"failure"`, or `"assumed"`.
    pub outcome: String,
    /// Source location.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// Condition kind (comparison, existence, truthiness, etc.).
    pub kind: String,
    /// Operator (for comparisons).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<String>,
    /// Left / actual operand.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub left: Option<OperandExplanation>,
    /// Right / expected operand.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub right: Option<OperandExplanation>,
    /// Loop or quantifier witness summary, when available.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub witness: Option<LoopWitnessExplanation>,
    /// For binding conditions (`:=`): the variable name being bound.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub binding_name: Option<String>,
    /// For Builtin kind: the builtin function name (`"startswith"`, `"endswith"`,
    /// `"contains"`). Populated only when `kind == "builtin"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub builtin_name: Option<String>,
    /// Orthogonal modifier: `true` when the condition's truth is inverted (e.g.
    /// `not X == Y` emits `kind: "comparison", negated: true`, and
    /// `not startswith(X, "foo")` emits `kind: "builtin", negated: true`). Omitted
    /// from serialized output when `false`, so positive conditions keep the same
    /// shape they had before this field existed.
    #[serde(default, skip_serializing_if = "is_false")]
    pub negated: bool,
    /// Constructs this condition was evaluated inside, outer to inner:
    /// `"comprehension"`, `"every"`, `"negation"`. Omitted for rule-level
    /// conditions. A scoped condition is per-iteration (or inverted) evidence,
    /// not a condition that decided the rule on its own: in
    /// `n := count([r | some r in input.resources; ...])` the `r` binding is
    /// one sample element, not the subject of the result.
    ///
    /// Scopes are relative to the rule body that recorded the condition, so
    /// entries in `helper_conditions` are relative to the helper's body; the
    /// calling condition's own `scopes` apply to them too. Rego only: Azure
    /// Policy conditions never carry scopes.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub scopes: Vec<&'static str>,
    /// For a condition that checks a rule or function call, directly or through
    /// `not`: the full name of the called rule (for example
    /// `"data.policy._secure"`), which `helper_conditions` belong to. Present
    /// even when those conditions were not expanded. Omitted otherwise.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub helper_rule: Option<String>,
    /// For truthiness conditions whose backing register was written by a
    /// `CallRule` (i.e. the customer wrote `not _helper(x)` or bare
    /// `_helper(x)` as a guard), this carries the helper's evaluated inner
    /// conditions structurally so consumers can render "Violation caused by:
    /// …" inline. Populated at materialize time by walking chronological
    /// `condition_outcomes` between the `CallRule` and outer `Guard`,
    /// filtered by `rule_index == helper_idx`. Omitted from serialized
    /// output when empty. Bounded by the `MAX_HELPER_DEPTH` recursion guard for
    /// nested helpers.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub helper_conditions: Vec<ConditionExplanation>,
    /// `true` when this condition had a helper call behind it that was not
    /// expanded because `MAX_HELPER_DEPTH` was reached. Distinguishes "there
    /// is nothing behind this condition" from "there was more and we stopped",
    /// which are otherwise identical in the output. Omitted when `false`.
    #[serde(default, skip_serializing_if = "is_false")]
    pub helper_conditions_truncated: bool,
}

/// Serde skip helper: omit the field when the boolean is `false`.
const fn is_false(b: &bool) -> bool {
    !*b
}

/// Summary of a completed loop, attached to the last reported condition of
/// what it helps explain.
///
/// A loop is anchored at the last condition its own rule body recorded while
/// it ran; a loop with no such condition is never summarized. A definition (or
/// a rule-less program, or a helper body) carries the latest loop anchored
/// among its reported conditions. An emission or derivation additionally
/// requires that the loop finished before the value was emitted and that its
/// enclosing loop iteration, if any, was still running at the emission, so the
/// loop that produced a value is summarized on its definition, never on the
/// emission.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[non_exhaustive]
pub struct LoopWitnessExplanation {
    pub total_iterations: u32,
    pub success_count: u32,
    /// Key of the first successful iteration.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sample_key: Option<Value>,
    /// Value of the first successful iteration.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sample_value: Option<Value>,
    /// Whether redaction changed the sample (`Redacted` value mode).
    #[serde(default, skip_serializing_if = "is_false")]
    pub redacted: bool,
}

/// An operand value with optional provenance.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct OperandExplanation {
    /// The runtime value (may be redacted).
    pub value: Value,
    /// Data path, e.g. `"input.role"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub provenance: Option<String>,
    /// A negated reference was undefined, rather than a defined false value.
    #[serde(default, skip_serializing_if = "is_false")]
    pub absent: bool,
    /// `value` is a prefix of a larger collection, cut to the report's element
    /// budget (`MAX_OPERAND_ELEMENTS`, counted across nesting).
    #[serde(default, skip_serializing_if = "is_false")]
    pub truncated: bool,
    /// When `truncated`, the original top-level element count of `value`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub length: Option<usize>,
    /// Whether the value was redacted.
    pub redacted: bool,
    /// Fully-qualified Azure Policy alias name this value was compiled from,
    /// e.g. `"Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly"`.
    /// Lets a consumer map straight to the alias's ARM `defaultPath` instead
    /// of inverting the (lower-cased, `properties`-flattened) `provenance`
    /// path above. Absent for non-Azure-Policy conditions and for values not
    /// compiled from an alias.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_alias: Option<String>,
}

/// Source location.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct SourceLocation {
    pub file: String,
    pub row: usize,
    pub col: usize,
}

/// A recorded assumption for the output.
#[derive(Debug, Clone, Serialize)]
pub struct AssumptionRecord {
    /// Kind of assumption.
    pub kind: String,
    /// Input path that was assumed.
    pub input_path: String,
    /// Condition text that was assumed to hold.
    pub assumed_holds: String,
    /// The comparison operator (e.g. "==", "!="), if applicable.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<String>,
    /// The non-input value that was compared against.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assumed_value: Option<Value>,
    /// Source location.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// `true` when `assumed_value` was rewritten by redaction.
    #[serde(default, skip_serializing_if = "is_false")]
    pub redacted: bool,
}

// ---------------------------------------------------------------------------
// Partial Evaluation Output
// ---------------------------------------------------------------------------

/// A single condition in a PE residual query.
#[derive(Debug, Clone, Serialize)]
pub struct ResidualCondition {
    /// The condition text, e.g. `"input.document.status == \"public\""`.
    pub condition: String,
    /// The comparison operator, e.g. `"=="`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operator: Option<String>,
    /// The operator as the policy author wrote it, when it differs from the
    /// normalized symbol in `operator` (Azure Policy's `notEquals` vs `!=`).
    /// Mirrors `ConditionExplanation::builtin_name` so a consumer can render
    /// residuals in the authoring language without parsing source text.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub builtin_name: Option<String>,
    /// The input path that is unknown, e.g. `"input.document.status"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub input_path: Option<String>,
    /// The concrete value being compared against.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub value: Option<Value>,
    /// Kind of assumption.
    pub kind: String,
    /// For `negation_holds` conditions: the inner conditions that the negation
    /// wraps.  Semantics: "NOT (all of negated_conditions hold simultaneously)".
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub negated_conditions: Vec<ResidualCondition>,
    /// Fully-qualified rule name that produced this residual condition,
    /// e.g. `"data.bicep.deny"`.  Lets consumers attribute a disjunct back
    /// to the rule (and rule definition) that contributed it without
    /// re-running PE per rule.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_rule: Option<String>,
    /// Source file where the condition appears, e.g. `"policy.rego"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_file: Option<String>,
    /// 1-based source line for the condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_row: Option<u32>,
    /// 1-based source column for the condition.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_col: Option<u32>,
    /// 1-based source line of the FIRST instruction of the rule body
    /// (definition) that produced this condition.  Mirrors the value reported
    /// by `DefinitionExplanation.location.row` in the causality report, so
    /// consumers can exact-match a PE residual conjunct to the rule body it
    /// came from — including the multi-body same-name rule case.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_rule_start_row: Option<u32>,
    /// Calling rule frames, outermost first, present when this condition was
    /// recorded inside a helper that another rule invoked. `call_chain[0]` is
    /// the rule that owns the residual at any call depth, which is the key a
    /// consumer joins a residual back to its violation on; `source_rule`
    /// continues to name the callee that recorded it, and is never duplicated
    /// into the chain. Absent for a condition recorded directly in a rule body.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub call_chain: Vec<CallFrameInfo>,
    /// True when `call_chain` was cut off at `MAX_HELPER_DEPTH` and deeper
    /// calling frames exist but are not reported. Mirrors
    /// `ConditionExplanation::helper_conditions_truncated` so the two
    /// explanation surfaces agree on how deep they follow helper calls, and so
    /// a short chain caused by the cap is distinguishable from a genuinely
    /// short one. `call_chain[0]` is retained regardless, because it is the key
    /// consumers join a residual back to its violation on.
    #[serde(skip_serializing_if = "core::ops::Not::not")]
    pub call_chain_truncated: bool,
}

/// One calling rule frame for a residual recorded inside a helper.
#[derive(Debug, Clone, Serialize)]
pub struct CallFrameInfo {
    /// Fully-qualified name of the calling rule, e.g. `"data.bicep.deny"`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule: Option<String>,
    /// Source file declaring the calling rule's body. Carried alongside the
    /// name and row because a helper may live in a different file from its
    /// caller, and a consumer that scopes a body match by file would
    /// otherwise fail to attribute the residual.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule_file: Option<String>,
    /// 1-based line of the first instruction of the calling rule's active
    /// body. Carried because a name alone cannot distinguish two bodies of a
    /// same-named rule, and a consumer that matches bodies needs both.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule_start_row: Option<u32>,
    /// 1-based line of the call site inside this frame.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub call_row: Option<u32>,
}

/// Result of partial evaluation.
#[derive(Debug, Clone, Serialize)]
pub struct PartialEvalResult {
    /// The query result: `true`, `false`, or `null` (for undefined).
    pub result: Value,
    /// DNF residual queries: outer vec is OR, inner vec is AND.
    pub residual_queries: Vec<Vec<ResidualCondition>>,
    /// Non-fatal caveats about this result. Consumers should switch on
    /// `code`; `message` carries engine-internal detail and is not
    /// author-facing.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub warnings: Vec<crate::evaluation_trace::PartialEvalWarning>,
}

/// Grouping metadata for one residual disjunct, taken from the assumptions
/// that formed it. Every assumption recorded in the same conjunction scope
/// shares these, so the first one seen describes the whole group.
#[derive(Clone)]
struct GroupMeta {
    conjunction_id: u32,
    /// Conjunctions of the calling frames, innermost first. A whole chain is
    /// kept rather than just the immediate caller because an intermediate rule
    /// that contributed no conditions of its own produces no group, so the
    /// nearest *existing* ancestor is what this group folds into.
    caller_conjunctions: Vec<u32>,
    rule_index: u16,
}

/// Describe the conjunction scope an assumption was recorded in.
fn group_meta_of(a: &crate::evaluation_trace::Assumption) -> GroupMeta {
    GroupMeta {
        conjunction_id: a.conjunction_id,
        caller_conjunctions: a
            .call_chain
            .iter()
            .rev()
            .map(|frame| frame.conjunction_id)
            .collect(),
        rule_index: a.rule_index,
    }
}

/// Upper bound on disjuncts in a distributed residual. Distribution is
/// multiplicative, so without a bound a policy with several multi-definition
/// helpers could expand far enough to be a denial-of-service surface.
const MAX_RESIDUAL_DISJUNCTS: usize = 1024;

/// Depth guard for pathological call nesting. Rego rejects recursive rules, so
/// this bounds unexpected shapes rather than legitimate ones.
const MAX_DISTRIBUTION_DEPTH: usize = 32;

/// Fold each called rule's residual back into the conjunction that called it.
///
/// A called rule is a *conjunct* of its caller, while a rule with several
/// definitions is itself a *disjunction*. Folding is therefore a distribution:
/// `a AND (X OR Y)` becomes `(a AND X) OR (a AND Y)`. Without it, a condition
/// wrapped in a helper becomes a sibling disjunct and the residual claims the
/// policy applies under conditions it does not.
///
/// Returns `None` when the result would exceed [`MAX_RESIDUAL_DISJUNCTS`], so
/// the caller can fall back to the undistributed grouping. That fallback is
/// broader than the truth rather than narrower, which keeps a finding visible
/// instead of hiding one.
fn distribute_call_conjunctions(
    groups: &[(GroupMeta, Vec<ResidualCondition>)],
) -> Option<Vec<Vec<ResidualCondition>>> {
    let produced_a_group: alloc::collections::BTreeSet<u32> =
        groups.iter().map(|(meta, _)| meta.conjunction_id).collect();

    // Children keyed by the nearest ancestor conjunction that produced a group.
    let mut children: alloc::collections::BTreeMap<u32, Vec<usize>> =
        alloc::collections::BTreeMap::new();
    // Groups whose callers contributed no conditions at all still constrain
    // each other, so they are folded together under their outermost frame
    // rather than left as independent alternatives.
    let mut orphan_buckets: alloc::collections::BTreeMap<u32, Vec<usize>> =
        alloc::collections::BTreeMap::new();
    let mut roots: Vec<usize> = Vec::new();

    for (idx, (meta, _)) in groups.iter().enumerate() {
        let Some(outermost) = meta.caller_conjunctions.last().copied() else {
            roots.push(idx);
            continue;
        };
        match meta
            .caller_conjunctions
            .iter()
            .find(|conjunction| produced_a_group.contains(conjunction))
        {
            Some(parent) => children.entry(*parent).or_default().push(idx),
            None => orphan_buckets.entry(outermost).or_default().push(idx),
        }
    }

    let mut out: Vec<Vec<ResidualCondition>> = Vec::new();
    for idx in roots {
        out.extend(resolve_group(groups, &children, idx, 0)?);
        if out.len() > MAX_RESIDUAL_DISJUNCTS {
            return None;
        }
    }
    for (_, bucket) in orphan_buckets {
        out.extend(fold_children(groups, &children, Vec::new(), &bucket, 0)?);
        if out.len() > MAX_RESIDUAL_DISJUNCTS {
            return None;
        }
    }

    // A conjunction with no conditions is trivially true and would make the
    // whole residual vacuous.
    out.retain(|conjunction| !conjunction.is_empty());
    Some(out)
}

/// Expand one group into its alternatives, folding in every rule it called.
fn resolve_group(
    groups: &[(GroupMeta, Vec<ResidualCondition>)],
    children: &alloc::collections::BTreeMap<u32, Vec<usize>>,
    idx: usize,
    depth: usize,
) -> Option<Vec<Vec<ResidualCondition>>> {
    let (meta, conds) = groups.get(idx)?;
    let called = children
        .get(&meta.conjunction_id)
        .map(Vec::as_slice)
        .unwrap_or(&[]);
    fold_children(groups, children, conds.clone(), called, depth)
}

/// Multiply `base` by every called rule reachable from it.
///
/// Definitions of the same callee are alternatives and are OR-ed; distinct
/// callees are conjuncts, so each one multiplies the accumulator in turn.
fn fold_children(
    groups: &[(GroupMeta, Vec<ResidualCondition>)],
    children: &alloc::collections::BTreeMap<u32, Vec<usize>>,
    base: Vec<ResidualCondition>,
    child_indexes: &[usize],
    depth: usize,
) -> Option<Vec<Vec<ResidualCondition>>> {
    if depth >= MAX_DISTRIBUTION_DEPTH {
        return None;
    }

    let mut by_callee: alloc::collections::BTreeMap<u16, Vec<usize>> =
        alloc::collections::BTreeMap::new();
    for &child in child_indexes {
        if let Some((child_meta, _)) = groups.get(child) {
            by_callee
                .entry(child_meta.rule_index)
                .or_default()
                .push(child);
        }
    }

    let mut acc: Vec<Vec<ResidualCondition>> = alloc::vec![base];
    for (_, callee_groups) in by_callee {
        let mut alternatives: Vec<Vec<ResidualCondition>> = Vec::new();
        for child in callee_groups {
            alternatives.extend(resolve_group(
                groups,
                children,
                child,
                depth.saturating_add(1),
            )?);
        }
        if alternatives.is_empty() {
            continue;
        }
        let mut next: Vec<Vec<ResidualCondition>> = Vec::new();
        for existing in &acc {
            for alternative in &alternatives {
                if next.len() >= MAX_RESIDUAL_DISJUNCTS {
                    return None;
                }
                let mut merged = existing.clone();
                merged.extend(alternative.iter().cloned());
                next.push(merged);
            }
        }
        acc = next;
    }
    Some(acc)
}

/// Produce a [`PartialEvalResult`] from a program and its evaluation trace.
pub fn materialize_pe(
    program: &Program,
    trace: &EvaluationTrace,
    query_result: Value,
) -> PartialEvalResult {
    // If the result is fully determined (at least one definition succeeded
    // without any assumptions), skip residual computation.
    if trace.definitive_result {
        let result = match query_result {
            Value::Undefined => Value::Null,
            other => other,
        };
        return PartialEvalResult {
            result,
            residual_queries: Vec::new(),
            warnings: trace.warnings.clone(),
        };
    }

    use alloc::collections::BTreeMap;

    // -----------------------------------------------------------------------
    // 1. Collect negation-scoped inner assumptions into a side-map.
    //    Assumptions with `negation_scope_id = Some(id)` are inner conditions
    //    of a `not` body.  They should NOT appear as top-level disjunct
    //    conditions; instead they are attached to the parent NegationHolds
    //    condition that shares the same scope id.
    // -----------------------------------------------------------------------
    let mut negation_inner: BTreeMap<u32, Vec<ResidualCondition>> = BTreeMap::new();

    // Group assumptions by (conjunction_id, iteration_index) to form disjuncts.
    // Each unique combination produces one conjunction (AND) in the DNF output.
    let mut disjunct_map: BTreeMap<(u32, Option<u32>), (GroupMeta, Vec<ResidualCondition>)> =
        BTreeMap::new();

    // First pass: collect inner-negation assumptions into negation_inner.
    for a in &trace.assumptions {
        // An assumption is orphaned when its enclosing definition (or any
        // enclosing definition on the call stack) failed to emit / assign
        // a value, meaning the assumption cannot have caused any observable
        // effect.
        if a.orphaned {
            continue;
        }
        if let Some(neg_scope) = a.negation_scope_id {
            let cond = assumption_to_residual(a, program);
            negation_inner.entry(neg_scope).or_default().push(cond);
        }
    }

    // Second pass: build disjuncts from top-level (non-negation-inner) assumptions.
    for a in &trace.assumptions {
        // Skip orphaned assumptions (see comment on first pass above).
        if a.orphaned {
            continue;
        }
        // Skip assumptions that belong inside a negation body — they will be
        // attached to the NegationHolds parent below.
        if a.negation_scope_id.is_some() {
            continue;
        }

        let key = (a.conjunction_id, a.iteration_index);

        // For NegationHolds: single condition with inner children.
        if a.kind == AssumptionKind::NegationHolds {
            let mut cond = assumption_to_residual(a, program);
            if let Some(scope_id) = a.owned_negation_scope_id {
                if let Some(mut inner) = negation_inner.remove(&scope_id) {
                    attach_nested_negation_inner(&mut inner, &mut negation_inner);
                    cond.negated_conditions = inner;
                }
            }
            disjunct_map
                .entry(key)
                .or_insert_with(|| (group_meta_of(a), Vec::new()))
                .1
                .push(cond);
            continue;
        }

        // Try data-key inversion (may produce multiple conditions).
        let inverted = assumption_to_residual_conditions(a, program);
        if inverted.len() > 1 {
            // Multiple matching keys → each becomes a separate disjunct
            // so the overall result is OR(key1, key2, ...).
            // We tag them with synthetic iteration indices to separate them.
            for (i, cond) in inverted.into_iter().enumerate() {
                let offset = u32::try_from(i).unwrap_or(u32::MAX);
                let split_key = (
                    key.0,
                    Some(
                        key.1
                            .unwrap_or(0)
                            .wrapping_add(1000_u32.wrapping_add(offset)),
                    ),
                );
                disjunct_map
                    .entry(split_key)
                    .or_insert_with(|| (group_meta_of(a), Vec::new()))
                    .1
                    .push(cond);
            }
        } else {
            for cond in inverted {
                disjunct_map
                    .entry(key)
                    .or_insert_with(|| (group_meta_of(a), Vec::new()))
                    .1
                    .push(cond);
            }
        }
    }

    // Deduplicate conditions within each disjunct.
    // Also drop empty `negation_holds` placeholders (PE-2): when a rule
    // fires concretely the recorded NegationHolds assumption may carry no
    // input path, no operator, and no inner conditions.  Such a placeholder
    // provides no information to consumers and prevents the disjunct from
    // collapsing to an empty (always-true) clause.
    //
    // The filter recurses into `negated_conditions[]` so empty placeholders
    // nested inside another `negation_holds` are also dropped;
    // `attach_nested_negation_inner` above assigns the inner arrays but
    // doesn't filter them.
    let groups: Vec<(GroupMeta, Vec<ResidualCondition>)> = disjunct_map
        .into_values()
        .filter_map(|(meta, mut conds)| {
            conds.dedup_by(|a, b| a.condition == b.condition && a.operator == b.operator);
            filter_empty_placeholders_recursive(&mut conds);
            if conds.is_empty() {
                None
            } else {
                Some((meta, conds))
            }
        })
        .collect();

    let mut warnings = trace.warnings.clone();
    let residual_queries = distribute_call_conjunctions(&groups).unwrap_or_else(|| {
        warnings.push(crate::evaluation_trace::PartialEvalWarning {
            code: crate::evaluation_trace::PartialEvalWarningCode::DistributionOverflow,
            message: "residual could not be distributed within the disjunct limit; conditions \
                      from called rules are reported as separate alternatives, which is broader \
                      than the policy requires"
                .to_string(),
        });
        groups.iter().map(|(_, conds)| conds.clone()).collect()
    });

    let result = match query_result {
        Value::Undefined => Value::Null,
        other => other,
    };

    PartialEvalResult {
        result,
        residual_queries,
        warnings,
    }
}

/// Format a `Value` for display in condition text.
fn format_value(v: &Value) -> alloc::string::String {
    match v {
        Value::String(s) => alloc::format!("\"{}\"", s),
        Value::Null => "null".into(),
        Value::Bool(b) => alloc::format!("{b}"),
        Value::Number(n) => alloc::format!("{:?}", n),
        _ => alloc::format!("{:?}", v),
    }
}

/// Convert an `Assumption` to a `ResidualCondition`.
/// When the assumption has a `data_lookup_context`, inverts the lookup:
/// instead of `data.perms[input.role] == "write"`, produces one or more
/// conditions like `input.role == "admin"`.
fn assumption_to_residual_conditions(
    a: &crate::evaluation_trace::Assumption,
    program: &Program,
) -> Vec<ResidualCondition> {
    let (source_rule, source_file, source_row, source_col, source_rule_start_row) =
        source_attribution(a, program);

    // Check for data-key inversion.
    if let (Some(ref ctx), Some(ref cmp_value), Some(ref op)) =
        (&a.data_lookup_context, &a.assumed_value, &a.operator)
    {
        if let Value::Object(ref obj) = ctx.data_object {
            let matching_keys: Vec<&Value> = obj
                .iter()
                .filter(|(_, v)| match op.as_str() {
                    "==" => *v == cmp_value,
                    "!=" => *v != cmp_value,
                    _ => false,
                })
                .map(|(k, _)| k)
                .collect();

            if !matching_keys.is_empty() {
                let (call_chain, call_chain_truncated) = call_chain_attribution(a, program);
                return matching_keys
                    .into_iter()
                    .map(|key| {
                        let inverted_op = match op.as_str() {
                            "!=" => "!=", // preserve != semantics
                            _ => "==",
                        };
                        ResidualCondition {
                            condition: alloc::format!(
                                "{} {} {}",
                                ctx.key_input_path,
                                inverted_op,
                                format_value(key),
                            ),
                            operator: Some(inverted_op.to_string()),
                            // Data-key inversion rewrites the operator, so the
                            // authored form no longer describes this condition.
                            builtin_name: None,
                            input_path: Some(ctx.key_input_path.clone()),
                            value: Some(key.clone()),
                            kind: "condition_holds".to_string(),
                            negated_conditions: Vec::new(),
                            source_rule: source_rule.clone(),
                            source_file: source_file.clone(),
                            source_row,
                            source_col,
                            source_rule_start_row,
                            call_chain: call_chain.clone(),
                            call_chain_truncated,
                        }
                    })
                    .collect();
            }
        }
    }

    // Default: no inversion, return single condition.
    alloc::vec![assumption_to_residual(a, program)]
}

/// Convert an `Assumption` to a single `ResidualCondition` (no inversion).
fn assumption_to_residual(
    a: &crate::evaluation_trace::Assumption,
    program: &Program,
) -> ResidualCondition {
    let kind_str = match a.kind {
        AssumptionKind::Exists => "exists",
        AssumptionKind::ConditionHolds => "condition_holds",
        AssumptionKind::CollectionExists => "collection_exists",
        AssumptionKind::NegationHolds => "negation_holds",
    };
    let (source_rule, source_file, source_row, source_col, source_rule_start_row) =
        source_attribution(a, program);
    let (call_chain, call_chain_truncated) = call_chain_attribution(a, program);
    ResidualCondition {
        condition: residual_condition_text(a, program),
        operator: a.operator.clone(),
        builtin_name: a.builtin_name.clone(),
        // Strip the trailing `[_]` iteration marker from `input_path` on
        // `exists` and `condition_holds` kinds. The `[_]` originates in
        // `rvm/vm/loops.rs`'s phantom-iteration setup (`element_path = base + "[_]"`
        // tainting the iterator's value-register provenance) and propagates
        // through Guard/comparison assumption recording. It's an engine-internal
        // iterator variable placeholder with no meaning to a policy author.
        // `collection_exists` is already clean (recorded pre-taint from the base
        // path); `negation_holds` carries an empty `input_path`.
        input_path: if a.input_path.is_empty() {
            None
        } else {
            Some(match kind_str {
                "exists" | "condition_holds" => strip_iteration_suffix(&a.input_path),
                _ => a.input_path.clone(),
            })
        },
        value: a.assumed_value.clone(),
        kind: kind_str.to_string(),
        negated_conditions: Vec::new(),
        source_rule,
        source_file,
        source_row,
        source_col,
        source_rule_start_row,
        call_chain,
        call_chain_truncated,
    }
}

/// Strip a trailing `[_]` iterator placeholder from an input path.
/// Returns the base collection path when the suffix is present; otherwise
/// clones the input unchanged.
fn strip_iteration_suffix(path: &str) -> String {
    path.strip_suffix("[_]").unwrap_or(path).to_string()
}

/// Name a program that has no rule structure, from the compiler's definition
/// metadata. Shared by causality's synthetic rule and PE's residual source
/// attribution so a consumer can join the two on the same string.
fn ruleless_program_name(program: &Program) -> alloc::string::String {
    ["display_name", "policy_name", "policy_id"]
        .iter()
        .find_map(|key| {
            program
                .metadata
                .annotations
                .get(*key)
                .and_then(|v| v.as_string().ok())
                .map(|s| s.as_ref().to_string())
        })
        .unwrap_or_else(|| alloc::string::String::from("policy"))
}

/// `(rule_name, source_file, row, col, rule_start_row)` for an assumption.
type SourceAttribution = (
    Option<String>,
    Option<String>,
    Option<u32>,
    Option<u32>,
    Option<u32>,
);

/// Look up (rule_name, source_file, row, col, rule_start_row) for an assumption.
fn source_attribution(
    a: &crate::evaluation_trace::Assumption,
    program: &Program,
) -> SourceAttribution {
    let rule_info = program.rule_infos.get(usize::from(a.rule_index));
    // A rule-less program (Azure Policy) has no `RuleInfo`, so name it the same
    // way causality names its synthetic rule — that string is the join key a
    // consumer uses to match a residual to its causality violation.
    let rule_name = match rule_info {
        Some(info) => Some(info.name.clone()),
        None if program.rule_infos.is_empty() => Some(ruleless_program_name(program)),
        None => None,
    };
    let pc_usize: usize = a.pc.try_into().unwrap_or(0);
    let (file, row, col) = program
        .instruction_spans
        .get(pc_usize)
        .and_then(Option::as_ref)
        .map(|span| {
            let file = program
                .sources
                .get(span.source_index)
                .map(|s| s.name.clone())
                .unwrap_or_default();
            (
                Some(file),
                Some(u32::try_from(span.line).unwrap_or(u32::MAX)),
                Some(u32::try_from(span.column).unwrap_or(u32::MAX)),
            )
        })
        .unwrap_or((None, None, None));
    // Mirror `materialize_definitions`: the rule-body row is the line of the
    // FIRST instruction of `RuleInfo.definitions[definition_index]`. Causality
    // already reports this as `DefinitionExplanation.location.row`, so a
    // consumer can join PE residual conjuncts to causality definitions by
    // exact equality on (rule_name, rule_start_row) — critical for the
    // multi-body same-name rule case.
    let rule_start_row = rule_body_start_row(program, a.rule_index, a.definition_index);
    (rule_name, file, row, col, rule_start_row)
}

/// 1-based line of the first instruction of a rule definition's body.
///
/// Shared by the recording rule's own attribution and by each calling frame
/// in `call_chain`, so both sides of a consumer's body-level join are computed
/// the same way rather than by two implementations that could drift.
fn rule_body_start_row(program: &Program, rule_index: u16, definition_index: u16) -> Option<u32> {
    rule_body_span(program, rule_index, definition_index)
        .map(|span| u32::try_from(span.line).unwrap_or(u32::MAX))
}

/// Span of the first instruction of a rule definition's body.
fn rule_body_span(
    program: &Program,
    rule_index: u16,
    definition_index: u16,
) -> Option<crate::rvm::program::SpanInfo> {
    program
        .rule_infos
        .get(usize::from(rule_index))
        .and_then(|info| info.definitions.get(usize::from(definition_index)))
        .and_then(|def_pcs| def_pcs.first().copied())
        .and_then(|first_pc| {
            let idx = usize::try_from(first_pc).unwrap_or(0);
            program.instruction_spans.get(idx).cloned()
        })
        .flatten()
}

/// Name of the source file a span belongs to.
fn span_source_name(program: &Program, span: &crate::rvm::program::SpanInfo) -> Option<String> {
    program
        .sources
        .get(span.source_index)
        .map(|source| source.name.clone())
}

/// 1-based source line for an instruction.
fn instruction_row(program: &Program, pc: u32) -> Option<u32> {
    let idx = usize::try_from(pc).unwrap_or(0);
    program
        .instruction_spans
        .get(idx)
        .and_then(Option::as_ref)
        .map(|span| u32::try_from(span.line).unwrap_or(u32::MAX))
}

/// Resolve the recorded calling frames into names, files and rows, outermost
/// first, bounded by `MAX_HELPER_DEPTH`.
///
/// The cap is applied *here*, on the reported chain, and deliberately not on
/// the recorded one: `group_meta_of` derives `caller_conjunctions` from the
/// full `Assumption::call_chain`, so truncating at record time would break the
/// DNF distribution's search for a parent group. Frames are dropped from the
/// deep end, which keeps `call_chain[0]` and matches how causality stops
/// descending rather than discarding its outermost context.
///
/// Returns the frames and whether any were dropped.
fn call_chain_attribution(
    a: &crate::evaluation_trace::Assumption,
    program: &Program,
) -> (Vec<CallFrameInfo>, bool) {
    let truncated = a.call_chain.len() > MAX_HELPER_DEPTH;
    let frames = a
        .call_chain
        .iter()
        .take(MAX_HELPER_DEPTH)
        .map(|frame| {
            let body_span = rule_body_span(program, frame.rule_index, frame.definition_index);
            CallFrameInfo {
                rule: program
                    .rule_infos
                    .get(usize::from(frame.rule_index))
                    .map(|info| info.name.clone()),
                rule_file: body_span
                    .as_ref()
                    .and_then(|span| span_source_name(program, span)),
                rule_start_row: body_span
                    .as_ref()
                    .map(|span| u32::try_from(span.line).unwrap_or(u32::MAX)),
                call_row: instruction_row(program, frame.call_pc),
            }
        })
        .collect();
    (frames, truncated)
}

/// Render a residual's condition text for display.
///
/// For a condition recorded inside a helper, the raw text is the helper's
/// *definition* — rule head plus formal parameter names — which describes the
/// helper rather than the check the caller actually requested. Reuse the
/// causality path's helper-body rewriting to drop the head and substitute the
/// caller's literal arguments, so both explanation surfaces phrase a
/// helper-gated condition the same way. A non-literal argument leaves the
/// parameter name in place rather than inventing a value.
fn residual_condition_text(a: &crate::evaluation_trace::Assumption, program: &Program) -> String {
    let raw = strip_trailing_comment(&a.condition_text);
    let Some(innermost) = a.call_chain.last() else {
        return raw;
    };
    // `extract_helper_arg_substitutions` locates the call by looking at the
    // instruction *before* the pc it is given, so hand it the slot after the
    // call site.
    let after_call_pc = usize::try_from(innermost.call_pc)
        .unwrap_or(0)
        .saturating_add(1);
    let substitutions = extract_helper_arg_substitutions(after_call_pc, a.rule_index, program);
    rewrite_helper_body_text(&raw, &substitutions)
}

/// Strip a trailing Rego comment (`# ...`) from a rendered condition string,
/// preserving the meaningful expression text.  Defensive against quoted
/// `#` characters: only strips if the `#` is outside any string literal.
fn strip_trailing_comment(text: &str) -> String {
    let mut in_string: Option<char> = None;
    let mut escape = false;
    let bytes = text.as_bytes();
    for (i, ch) in text.char_indices() {
        if escape {
            escape = false;
            continue;
        }
        match in_string {
            Some(q) => {
                if ch == '\\' {
                    escape = true;
                } else if ch == q {
                    in_string = None;
                }
            }
            None => {
                if ch == '"' || ch == '\'' {
                    in_string = Some(ch);
                } else if ch == '#' {
                    let _ = bytes;
                    return text[..i].trim_end().to_string();
                }
            }
        }
    }
    text.to_string()
}

/// Returns true if `cond` is an information-free placeholder that should be
/// dropped from the DNF output.  Today this matches a `negation_holds` entry
/// with no condition text, no input path, no operator, and no inner negated
/// conditions — i.e. a frame recorded for a `not <expr>` whose inner body
/// either resolved concretely or had no input dependency to attribute (PE-2).
fn is_empty_placeholder(cond: &ResidualCondition) -> bool {
    cond.kind == "negation_holds"
        && cond.condition.is_empty()
        && cond.input_path.is_none()
        && cond.operator.is_none()
        && cond.negated_conditions.is_empty()
}

/// Recursively drop empty `negation_holds` placeholders — both at
/// the current level and inside any `negated_conditions[]` array of a
/// nested `negation_holds` frame. Order matters: recurse into children
/// FIRST so an inner `negation_holds` that becomes empty after its own
/// children are filtered also gets dropped at this level.
fn filter_empty_placeholders_recursive(conditions: &mut Vec<ResidualCondition>) {
    for cond in conditions.iter_mut() {
        if cond.kind == "negation_holds" && !cond.negated_conditions.is_empty() {
            filter_empty_placeholders_recursive(&mut cond.negated_conditions);
        }
    }
    conditions.retain(|c| !is_empty_placeholder(c));
}

/// Recursively attach inner negation conditions to any `negation_holds`
/// entries within `conditions`.
fn attach_nested_negation_inner(
    conditions: &mut [ResidualCondition],
    negation_inner: &mut alloc::collections::BTreeMap<u32, Vec<ResidualCondition>>,
) {
    for cond in conditions.iter_mut() {
        if cond.kind == "negation_holds" {
            // The inner conditions for this nested NegationHolds were
            // collected in the first pass.  We need the owned_negation_scope_id
            // but ResidualCondition doesn't carry it.  However, since we
            // consume scopes in order (BTreeMap is sorted), the next available
            // scope is the correct one for the next NegationHolds encountered.
            if let Some((&scope_id, _)) = negation_inner.iter().next() {
                if let Some(mut inner) = negation_inner.remove(&scope_id) {
                    // Recurse for deeper nesting.
                    attach_nested_negation_inner(&mut inner, negation_inner);
                    cond.negated_conditions = inner;
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Materialization
// ---------------------------------------------------------------------------

/// Produce a [`CausalityReport`] from a program and its evaluation trace.
pub fn materialize(
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
    query_result: Value,
) -> CausalityReport {
    let mut rules = materialize_rules(program, trace, settings);
    // Azure Policy compiles to a flat `main` entry point with no `CallRule`, so
    // no rule outcome is ever recorded and the conditions would be discarded.
    // Gated on `rule_infos` being empty so a Rego program, which always has
    // rules, can never take this path.
    if rules.is_empty() && program.rule_infos.is_empty() && !trace.condition_outcomes.is_empty() {
        rules.push(materialize_ruleless_program(
            program,
            trace,
            settings,
            &query_result,
        ));
    }
    let assumptions = if settings.detail == ExplanationDetail::Compact {
        Vec::new()
    } else {
        materialize_assumptions(program, trace, settings)
    };

    CausalityReport {
        query_result,
        rules,
        assumptions,
    }
}

/// Build a single synthetic rule for a program that has no rule structure,
/// naming it from the compiler's definition metadata where available.
fn materialize_ruleless_program(
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
    query_result: &Value,
) -> RuleExplanation {
    let conditions = materialize_conditions(0, u32::MAX, program, trace, settings);
    let outcome = if conditions.iter().any(|c| c.outcome == "failure") {
        "failure"
    } else {
        "success"
    };
    let name = ruleless_program_name(program);

    RuleExplanation {
        name,
        rule_type: alloc::string::String::from("policy"),
        result: query_result.clone(),
        emissions: Vec::new(),
        definitions: alloc::vec![DefinitionExplanation {
            index: 0,
            outcome: alloc::string::String::from(outcome),
            location: None,
            conditions,
        }],
        redacted: false,
    }
}

fn materialize_rules(
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<RuleExplanation> {
    // Group rule outcomes by rule_index.
    let mut rules: Vec<RuleExplanation> = Vec::new();

    // Collect unique rule indices from outcomes.
    let mut seen_rules: Vec<u16> = Vec::new();
    for outcome in &trace.rule_outcomes {
        if !seen_rules.contains(&outcome.rule_index) {
            seen_rules.push(outcome.rule_index);
        }
    }

    let helper_sensitivity = (settings.value_mode == ValueMode::Redacted)
        .then(|| HelperSensitivity::new(program, trace));

    for rule_idx in &seen_rules {
        let rule_info = match program.rule_infos.get(usize::from(*rule_idx)) {
            Some(info) => info,
            None => continue,
        };

        // Find the final result for this rule.
        let result = trace
            .rule_outcomes
            .iter()
            .rev()
            .find(|o| o.rule_index == *rule_idx && o.succeeded)
            .and_then(|o| o.result_value_idx)
            .and_then(|idx| trace.get_value(idx))
            .cloned()
            .unwrap_or(Value::Undefined);

        let rule_type_str = match rule_info.rule_type {
            crate::rvm::program::RuleType::Complete => "complete",
            crate::rvm::program::RuleType::PartialSet => "partial_set",
            crate::rvm::program::RuleType::PartialObject => "partial_object",
        };

        let emissions = materialize_rule_emissions(*rule_idx, rule_info, program, trace, settings);
        let definitions = if settings.scope == ExplanationScope::RuleSummary
            || (settings.detail == ExplanationDetail::Compact
                && rule_info.rule_type == crate::rvm::program::RuleType::PartialSet
                && !emissions.is_empty())
        {
            Vec::new()
        } else {
            materialize_definitions(*rule_idx, rule_info, program, trace, settings)
        };

        let (result, redacted, emissions) = match helper_sensitivity
            .as_ref()
            .filter(|_| !is_output_rule(&rule_info.name, program))
        {
            Some(sensitivity) => redact_helper_results(
                *rule_idx,
                &rule_info.name,
                result,
                emissions,
                sensitivity,
                trace,
            ),
            None => (result, false, emissions),
        };

        rules.push(RuleExplanation {
            name: rule_info.name.clone(),
            rule_type: rule_type_str.to_string(),
            result,
            emissions,
            definitions,
            redacted,
        });
    }

    rules
}

/// Redact the results of a helper rule the caller did not query, like an
/// operand, and report whether each was rewritten.
///
/// A value read from a sensitive path (the rule's recorded result path, or an
/// emitted value's path) is hidden whole, and so is any element of the rule's
/// collection result that equals such an emitted value. A value of a
/// sensitively named rule is hidden whole unless it is a boolean or null,
/// which describe a setting rather than hold one. Any other value has its
/// nested secrets sanitized. Runs after derivations are attached, because
/// derivation matching compares the raw emitted values.
fn redact_helper_results(
    rule_idx: u16,
    rule_name: &str,
    result: Value,
    mut emissions: Vec<EmissionExplanation>,
    sensitivity: &HelperSensitivity<'_>,
    trace: &EvaluationTrace,
) -> (Value, bool, Vec<EmissionExplanation>) {
    let name_sensitive = rule_name.rsplit('.').next().is_some_and(is_sensitive_name);
    let rule = usize::from(rule_idx);
    let result_path_sensitive = sensitivity
        .result_path_sensitive
        .get(rule)
        .copied()
        .unwrap_or(false);
    let empty = alloc::collections::BTreeSet::new();
    let sensitive_emissions = sensitivity.sensitive_emissions.get(rule).unwrap_or(&empty);

    let redact = |value: Value, path_sensitive: bool| -> (Value, bool) {
        if matches!(value, Value::Undefined) {
            return (value, false);
        }
        let whole =
            path_sensitive || (name_sensitive && !matches!(value, Value::Bool(_) | Value::Null));
        sanitize_value(&value, whole, trace).map_or((value, false), |sanitized| (sanitized, true))
    };

    for emission in &mut emissions {
        let path_sensitive = sensitive_emissions.contains(&&emission.result);
        let (value, redacted) = redact(
            core::mem::replace(&mut emission.result, Value::Undefined),
            path_sensitive,
        );
        emission.result = value;
        emission.redacted = redacted;
    }

    let (result, hid_elements) = hide_sensitive_elements(result, sensitive_emissions, trace);
    let result_is_key = is_sensitive_key(&result, false, trace);
    let (result, redacted) = redact(result, result_path_sensitive || result_is_key);
    (result, redacted || hid_elements, emissions)
}

/// Where each rule's results came from, gathered in one pass over the trace:
/// whether its latest summary result was read from a sensitive path, and the
/// emitted values that were (or are keys of a sensitive collection).
struct HelperSensitivity<'a> {
    result_path_sensitive: Vec<bool>,
    sensitive_emissions: Vec<alloc::collections::BTreeSet<&'a Value>>,
}

impl<'a> HelperSensitivity<'a> {
    fn new(program: &Program, trace: &'a EvaluationTrace) -> Self {
        let rules = program.rule_infos.len();
        let helper: Vec<bool> = program
            .rule_infos
            .iter()
            .map(|info| !is_output_rule(&info.name, program))
            .collect();
        let is_helper = |rule: u16| helper.get(usize::from(rule)).copied().unwrap_or(false);
        // Fail closed: a rule's one reported `result` stands for all of its
        // calls, so any successful call that returned a sensitive value makes
        // the result sensitive.
        let mut result_path_sensitive: Vec<bool> = alloc::vec![false; rules];
        for outcome in trace
            .rule_outcomes
            .iter()
            .filter(|o| o.is_summary && o.succeeded && is_helper(o.rule_index))
        {
            if let Some(slot) = result_path_sensitive.get_mut(usize::from(outcome.rule_index)) {
                if !*slot {
                    *slot = should_redact_runtime_path(outcome.result_path.as_deref(), trace);
                }
            }
        }
        let mut sensitive_emissions: Vec<alloc::collections::BTreeSet<&'a Value>> =
            alloc::vec![alloc::collections::BTreeSet::new(); rules];
        for emission in trace
            .emission_outcomes
            .iter()
            .filter(|emission| is_helper(emission.rule_index))
        {
            let Some(value) = emission.value_idx.and_then(|idx| trace.get_value(idx)) else {
                continue;
            };
            let sensitive = should_redact_runtime_path(emission.value_path.as_deref(), trace)
                || is_sensitive_key(value, emission.value_path.is_some(), trace);
            if sensitive {
                if let Some(slot) = sensitive_emissions.get_mut(usize::from(emission.rule_index)) {
                    slot.insert(value);
                }
            }
        }
        for leaf in trace
            .deep_object_leaves
            .iter()
            .filter(|leaf| is_helper(leaf.rule_index))
        {
            let Some(value) = leaf.value_idx.and_then(|idx| trace.get_value(idx)) else {
                continue;
            };
            if should_redact_runtime_path(leaf.value_path.as_deref(), trace)
                || is_sensitive_key(value, leaf.value_path.is_some(), trace)
            {
                if let Some(slot) = sensitive_emissions.get_mut(usize::from(leaf.rule_index)) {
                    slot.insert(value);
                }
            }
        }
        Self {
            result_path_sensitive,
            sensitive_emissions,
        }
    }
}

/// Replace the parts of a helper rule's collection result that equal one of
/// `hidden`, or that are keys of a sensitive collection, with `"<redacted>"`:
/// set and array elements, and object entry values at any depth (a multi-key
/// head nests them). An object keyed by such a key is hidden whole, since keys
/// cannot be rewritten without colliding.
fn hide_sensitive_elements(
    result: Value,
    hidden: &alloc::collections::BTreeSet<&Value>,
    trace: &EvaluationTrace,
) -> (Value, bool) {
    let check_keys = !trace.sensitive_keys.is_empty() || trace.sensitive_keys_overflowed;
    if hidden.is_empty() && !check_keys {
        return (result, false);
    }
    let mut changed = false;
    let rewritten = hide_sensitive_parts(&result, hidden, trace, 0, &mut changed);
    if changed {
        (rewritten, true)
    } else {
        (result, false)
    }
}

fn hide_sensitive_parts(
    value: &Value,
    hidden: &alloc::collections::BTreeSet<&Value>,
    trace: &EvaluationTrace,
    depth: usize,
    changed: &mut bool,
) -> Value {
    let next = depth.saturating_add(1);
    // Each part: hidden when sensitive itself, otherwise walked if it is a
    // collection, at every level.
    let part = |item: &Value, flag: &mut bool| {
        if hidden.contains(item) || is_sensitive_key(item, false, trace) {
            *flag = true;
            Value::from("<redacted>")
        } else if matches!(*item, Value::Object(_) | Value::Set(_) | Value::Array(_)) {
            hide_sensitive_parts(item, hidden, trace, next, flag)
        } else {
            item.clone()
        }
    };
    if depth >= MAX_REDACT_DEPTH {
        *changed = true;
        return Value::from("<redacted>");
    }
    match *value {
        Value::Set(ref items) => Value::from(
            items
                .iter()
                .map(|item| part(item, changed))
                .collect::<alloc::collections::BTreeSet<_>>(),
        ),
        Value::Array(ref items) => Value::from(
            items
                .iter()
                .map(|item| part(item, changed))
                .collect::<Vec<_>>(),
        ),
        Value::Object(ref map) => {
            if map.keys().any(|key| is_sensitive_key(key, false, trace)) {
                *changed = true;
                return Value::from("<redacted>");
            }
            Value::from(
                map.iter()
                    .map(|(key, item)| (key.clone(), part(item, changed)))
                    .collect::<alloc::collections::BTreeMap<_, _>>(),
            )
        }
        _ => value.clone(),
    }
}

fn materialize_definitions(
    rule_idx: u16,
    rule_info: &crate::rvm::program::RuleInfo,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<DefinitionExplanation> {
    let mut defs: Vec<DefinitionExplanation> = Vec::new();

    let def_outcomes: Vec<&RuleOutcome> = trace
        .rule_outcomes
        .iter()
        .filter(|o| o.rule_index == rule_idx && !o.is_summary)
        .collect();

    for outcome in &def_outcomes {
        let def_idx = outcome.definition_index;

        // Get instruction range for this definition.
        let body_pcs = rule_info
            .definitions
            .get(usize::from(def_idx))
            .cloned()
            .unwrap_or_default();

        let first_pc = body_pcs.first().copied().unwrap_or(0);

        let location = get_source_location(usize::try_from(first_pc).unwrap_or(0), program);

        // Find conditions within this definition's instruction range.
        let last_pc = find_rule_return_pc(usize::try_from(first_pc).unwrap_or(0), program);

        let conditions = materialize_conditions(first_pc, last_pc, program, trace, settings);

        defs.push(DefinitionExplanation {
            index: def_idx,
            outcome: if outcome.succeeded {
                "success".to_string()
            } else {
                "failure".to_string()
            },
            location,
            conditions,
        });
    }

    defs
}

fn materialize_rule_emissions(
    rule_idx: u16,
    rule_info: &crate::rvm::program::RuleInfo,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<EmissionExplanation> {
    if rule_info.rule_type != crate::rvm::program::RuleType::PartialSet {
        return Vec::new();
    }

    if settings.scope == ExplanationScope::RuleSummary {
        return Vec::new();
    }

    let mut emissions: Vec<EmissionExplanation> = Vec::new();
    let mut seen_results: Vec<Value> = Vec::new();
    let target_emission_index = if settings.scope == ExplanationScope::SingleEmission {
        settings.emission_index
    } else {
        None
    };
    let target_emission_value = if settings.scope == ExplanationScope::SingleEmission {
        settings.emission_value.as_ref()
    } else {
        None
    };
    let mut emission_index = 0_usize;

    for (position, emission) in trace
        .emission_outcomes
        .iter()
        .enumerate()
        .filter(|(_, outcome)| outcome.rule_index == rule_idx)
    {
        let Some(result) = emission
            .value_idx
            .and_then(|idx| trace.get_value(idx))
            .cloned()
        else {
            continue;
        };

        if seen_results.contains(&result) {
            continue;
        }

        if target_emission_index.is_some_and(|target_index| emission_index != target_index) {
            seen_results.push(result);
            emission_index = emission_index.saturating_add(1);
            continue;
        }

        if target_emission_value.is_some_and(|target_value| &result != target_value) {
            seen_results.push(result);
            emission_index = emission_index.saturating_add(1);
            continue;
        }

        seen_results.push(result.clone());

        emissions.push(EmissionExplanation {
            index: emission_index,
            definition_index: emission.definition_index,
            result,
            conditions: materialize_condition_window(
                emission.condition_start_index,
                emission.condition_end_index,
                emission.rule_index,
                position,
                program,
                trace,
                settings,
            ),
            derivations: Vec::new(),
            derivation_count: None,
            derivations_truncated: false,
            redacted: false,
        });

        emission_index = emission_index.saturating_add(1);

        if target_emission_index.is_some() {
            break;
        }
    }

    if settings.max_derivations > 1 {
        for explanation in &mut emissions {
            attach_derivations(explanation, rule_idx, program, trace, settings);
        }
    }

    emissions
}

/// Fill `explanation.derivations` with every distinct derivation of its value.
///
/// The trace records an emission each time a body adds a value to the set,
/// including values already present, so every derivation is available here.
/// Each derivation is materialized exactly like a top-level emission.
///
/// Exact duplicates (same definition and equal conditions as presented) add no
/// evidence and are dropped before counting. Equality is judged on conditions
/// materialized at `Standard` detail even when the report is `Compact`,
/// because `Compact` strips the operands that tell derivations apart; values
/// hidden by redaction, operand truncation or `PrimaryOnly` filtering are not
/// compared.
///
/// Only the first `max_derivations` distinct derivations are kept. Every later
/// derivation is still materialized, one at a time, to tell whether it is
/// distinct, and a 128-bit fingerprint is kept for each distinct one, so memory
/// grows by 16 bytes per distinct derivation past the cap and time grows with
/// the derivations' window sizes. Exact comparison against kept derivations
/// is linear in the cap, so a very large cap is quadratic in the number of
/// derivations.
///
/// The list is marked incomplete (`derivations_truncated`, with
/// `derivation_count` approximate) when an emission of the rule has no
/// captured value, which happens only once the trace's value capacity is
/// exhausted, and when a derivation past the cap cannot be fingerprinted.
fn attach_derivations(
    explanation: &mut EmissionExplanation,
    rule_idx: u16,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) {
    let identity_settings = (settings.detail == ExplanationDetail::Compact).then(|| {
        let mut identity = settings.clone();
        identity.detail = ExplanationDetail::Standard;
        identity
    });
    let mut kept: Vec<DerivationExplanation> = Vec::new();
    let mut kept_identities: Vec<DerivationExplanation> = Vec::new();
    let mut overflow: alloc::collections::BTreeSet<u128> = alloc::collections::BTreeSet::new();
    let mut total = 0_usize;
    let mut incomplete = false;

    for (position, emission) in trace
        .emission_outcomes
        .iter()
        .enumerate()
        .filter(|(_, outcome)| outcome.rule_index == rule_idx)
    {
        let Some(value) = emission.value_idx.and_then(|idx| trace.get_value(idx)) else {
            // The value was not captured, so this may be a derivation of it.
            incomplete = true;
            continue;
        };
        if *value != explanation.result {
            continue;
        }

        let window = |window_settings: &ExplanationSettings| DerivationExplanation {
            definition_index: emission.definition_index,
            conditions: materialize_condition_window(
                emission.condition_start_index,
                emission.condition_end_index,
                emission.rule_index,
                position,
                program,
                trace,
                window_settings,
            ),
        };
        let candidate = window(settings);
        let identity = identity_settings.as_ref().map(window);
        let key = identity.as_ref().unwrap_or(&candidate);

        let compared = if identity_settings.is_some() {
            &kept_identities
        } else {
            &kept
        };
        if compared.contains(key) {
            continue;
        }
        if kept.len() < settings.max_derivations {
            total = total.saturating_add(1);
            kept_identities.extend(identity);
            kept.push(candidate);
            continue;
        }
        match derivation_fingerprint(key) {
            Some(print) => {
                if overflow.insert(print) {
                    total = total.saturating_add(1);
                }
            }
            None => {
                total = total.saturating_add(1);
                incomplete = true;
            }
        }
    }

    if incomplete || total > settings.max_derivations {
        explanation.derivation_count = Some(total);
        explanation.derivations_truncated = true;
    }
    explanation.derivations = kept;
}
/// 128-bit FNV-1a fingerprint of a derivation, used only to recognize
/// duplicates beyond the retained cap.
///
/// The derivation's JSON carries its content, but JSON is not an equality
/// encoding of `Value` (arrays and sets serialize alike, as do number and
/// string object keys; `Undefined` is rendered as a string; integers beyond
/// 64 bits are rounded). A type-tag stream over every `Value` in the
/// derivation, with exact number content, is hashed too, so equal
/// fingerprints mean equal content and shape. Number content follows
/// `Number` equality except for integral floats beyond 2^53 compared with big
/// integers, where `Number` equality itself is lossy, and `-0.0`, which equals
/// `0` but prints differently (so it can count once more). A remaining hash
/// collision can at worst undercount `derivation_count`; it never changes
/// which derivations are reported.
fn derivation_fingerprint(derivation: &DerivationExplanation) -> Option<u128> {
    let mut hash = Fnv128::new();
    hash.write(&serde_json::to_vec(derivation).ok()?);
    for condition in &derivation.conditions {
        hash_condition_value_types(&mut hash, condition);
    }
    Some(hash.0)
}

struct Fnv128(u128);

impl Fnv128 {
    const fn new() -> Self {
        Self(0x6c62_272e_07bb_0142_62b8_2175_6295_c58d)
    }

    fn write(&mut self, bytes: &[u8]) {
        const PRIME: u128 = 0x0000_0000_0100_0000_0000_0000_0000_013b;
        for byte in bytes {
            self.0 = (self.0 ^ u128::from(*byte)).wrapping_mul(PRIME);
        }
    }
}

fn hash_condition_value_types(hash: &mut Fnv128, condition: &ConditionExplanation) {
    for operand in [&condition.left, &condition.right].into_iter().flatten() {
        hash_value_type(hash, &operand.value);
    }
    if let Some(witness) = &condition.witness {
        for value in [&witness.sample_key, &witness.sample_value]
            .into_iter()
            .flatten()
        {
            hash_value_type(hash, value);
        }
    }
    hash.write(b"(");
    for helper in &condition.helper_conditions {
        hash_condition_value_types(hash, helper);
    }
    hash.write(b")");
}

/// Hash the variant structure of `value`, plus exact number content (the JSON
/// rounds large integers). Other content is covered by the JSON. The walk is
/// iterative, so nesting depth neither overflows the stack
/// nor truncates the structure.
fn hash_value_type(hash: &mut Fnv128, root: &Value) {
    enum Step<'a> {
        Value(&'a Value),
        Close(&'static [u8]),
    }

    let mut stack = alloc::vec![Step::Value(root)];
    while let Some(step) = stack.pop() {
        let current = match step {
            Step::Close(tag) => {
                hash.write(tag);
                continue;
            }
            Step::Value(current) => current,
        };
        match current {
            Value::Null => hash.write(b"n"),
            Value::Bool(_) => hash.write(b"b"),
            Value::Number(number) => {
                // JSON rounds integers beyond 64 bits through f64, so hash the
                // exact decimal form; equal numbers share it.
                hash.write(b"#");
                hash.write(number.format_decimal().as_bytes());
                hash.write(b";");
            }
            Value::String(_) => hash.write(b"s"),
            Value::Undefined => hash.write(b"u"),
            Value::Array(items) => {
                hash.write(b"[");
                stack.push(Step::Close(b"]"));
                stack.extend(items.iter().rev().map(Step::Value));
            }
            Value::Set(items) => {
                hash.write(b"<");
                stack.push(Step::Close(b">"));
                let items: Vec<&Value> = items.iter().collect();
                stack.extend(items.into_iter().rev().map(Step::Value));
            }
            Value::Object(fields) => {
                hash.write(b"{");
                stack.push(Step::Close(b"}"));
                let fields: Vec<(&Value, &Value)> = fields.iter().collect();
                for (key, field) in fields.into_iter().rev() {
                    stack.push(Step::Value(field));
                    stack.push(Step::Value(key));
                }
            }
        }
    }
}
fn materialize_conditions(
    first_pc: u32,
    last_pc: u32,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<ConditionExplanation> {
    let relevant_outcomes = select_condition_outcomes(first_pc, last_pc, trace, settings);

    finalize_condition_explanations(
        materialize_condition_explanations(relevant_outcomes, program, trace, settings),
        settings,
        false,
    )
}

// ---------------------------------------------------------------------------
// Helper-boundary stitching
// ---------------------------------------------------------------------------

/// Maximum recursion depth when materializing nested helper bodies. Prevents
/// stack blow-up on pathological policies (mutually-recursive helpers).
const MAX_HELPER_DEPTH: usize = 8;

/// A rule or function call whose result a condition guard checks.
#[derive(Clone, Copy)]
struct HelperCall {
    rule_index: u16,
    /// The guard checks `not <call>` rather than the call result itself.
    through_not: bool,
}

impl HelperCall {
    /// Whether the helper definitely returned a falsy value (false or
    /// undefined), judged from the guarding condition's outcome: a direct
    /// guard fails, and a `not` guard holds, exactly when the helper was
    /// falsy. Anything else, including an `assumed` outcome, is not definite.
    /// (An assumption is recorded inside the helper, so the guard itself is
    /// not expected to be `assumed`.) In partial evaluation `not` also holds
    /// over a helper that held only by an assumption; callers rule that out
    /// with [`call_depends_on_assumption`].
    fn returned_falsy(self, outer_outcome: &str) -> bool {
        outer_outcome
            == if self.through_not {
                "success"
            } else {
                "failure"
            }
    }
}

/// If the Guard at `outer_pc` fires on a register written by a rule call
/// (either `CallRule` for a bare rule reference, or `FunctionCall` for a
/// helper-function call — the compiler picks `FunctionCall` for helpers with
/// arguments like `_frontdoor_has_waf(resource)`), return the call. Handles
/// both the positive `_helper(x)` and negated `not _helper(x)` forms (the
/// latter has a `Not` between the call and the Guard, recorded as
/// `through_not`). Returns `None` otherwise.
fn detect_helper_call_at_guard(outer_pc: usize, program: &Program) -> Option<HelperCall> {
    let guard = program.instructions.get(outer_pc)?;
    let guard_reg = match *guard {
        Instruction::Guard { register, .. } => register,
        _ => return None,
    };
    if outer_pc == 0 {
        return None;
    }
    let prev = program.instructions.get(outer_pc.saturating_sub(1))?;

    // Case 1: `_helper(x)` -- CallRule or FunctionCall writes directly to
    // the guard register.
    if let Some(rule_index) = call_writes_to(prev, guard_reg, program) {
        return Some(HelperCall {
            rule_index,
            through_not: false,
        });
    }

    // Case 2: `not _helper(x)` -- Not writes to the guard register from an
    // inner register that was in turn written by CallRule/FunctionCall.
    // Small lookback window mirrors `capture_builtin_guard_operands` in
    // `dispatch.rs`.
    if let Instruction::Not { dest, operand } = *prev {
        if dest == guard_reg && outer_pc >= 2 {
            const LOOKBACK: usize = 8;
            let start = outer_pc.saturating_sub(LOOKBACK).max(1);
            let mut cur = outer_pc.saturating_sub(1);
            while cur > start {
                cur = cur.saturating_sub(1);
                let candidate = program.instructions.get(cur)?;
                if let Some(rule_index) = call_writes_to(candidate, operand, program) {
                    return Some(HelperCall {
                        rule_index,
                        through_not: true,
                    });
                }
            }
        }
    }

    None
}

/// Returns the callee rule index if `instr` is a rule-call instruction
/// (`CallRule` or `FunctionCall`) writing to `target_reg`.
fn call_writes_to(instr: &Instruction, target_reg: u8, program: &Program) -> Option<u16> {
    match *instr {
        Instruction::CallRule { dest, rule_index } if dest == target_reg => Some(rule_index),
        Instruction::FunctionCall { params_index } => {
            let params = program
                .instruction_data
                .function_call_params
                .get(usize::from(params_index))?;
            (params.dest == target_reg).then_some(params.func_rule_index)
        }
        _ => None,
    }
}

/// Walk `trace.condition_outcomes` backward from `outer_outcome_idx`,
/// collecting outcomes whose `rule_index == helper_rule_index`. Stops when it
/// hits an outcome from `outer_rule_index` (marking the boundary where helper
/// execution began). Returns them in original chronological order.
fn collect_helper_condition_outcomes(
    outer_outcome_idx: usize,
    outer_rule_index: u16,
    helper_rule_index: u16,
    trace: &EvaluationTrace,
) -> Vec<(usize, &ConditionOutcome)> {
    if outer_outcome_idx == 0 {
        return Vec::new();
    }
    let mut collected: Vec<(usize, &ConditionOutcome)> = Vec::new();
    let mut idx = outer_outcome_idx;
    while idx > 0 {
        idx = idx.saturating_sub(1);
        let Some(outcome) = trace.condition_outcomes.get(idx) else {
            break;
        };
        if outcome.rule_index == outer_rule_index {
            break;
        }
        if outcome.rule_index == helper_rule_index {
            collected.push((idx, outcome));
        }
    }
    collected.reverse();
    collected
}

/// For a truthiness outer condition on a `Guard` whose backing register was
/// written by a rule call, materialize the helper's evaluated inner
/// conditions as structural children.
///
/// Returns the conditions, whether expansion was cut short by the depth cap,
/// and the detected call. Detection deliberately runs *before* the cap check
/// so the two empty cases stay distinguishable: no helper call at all reports
/// `false`, while a real helper we declined to expand reports `true`.
#[allow(clippy::too_many_arguments)]
fn materialize_helper_conditions(
    outer_pc: usize,
    outer_outcome_idx: usize,
    outer_rule_index: u16,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
    depth: usize,
) -> (Vec<ConditionExplanation>, bool, Option<HelperCall>) {
    let Some(call) = detect_helper_call_at_guard(outer_pc, program) else {
        return (Vec::new(), false, None);
    };
    let helper_rule_index = call.rule_index;
    if depth >= MAX_HELPER_DEPTH {
        return (Vec::new(), true, Some(call));
    }
    let inner_outcomes = collect_helper_condition_outcomes(
        outer_outcome_idx,
        outer_rule_index,
        helper_rule_index,
        trace,
    );
    if inner_outcomes.is_empty() {
        return (Vec::new(), false, Some(call));
    }
    let mut inner = materialize_condition_explanations_at_depth(
        inner_outcomes,
        program,
        trace,
        settings,
        depth.saturating_add(1),
        WitnessScope::Reported,
    );

    // Rewrite each inner condition's `text` to just the helper body
    // expression (drop rule head `<name>(params) if `) and substitute helper
    // parameter names with the caller's argument literals extracted from the
    // FunctionCall opcode preceding `outer_pc`. Turns
    // `in_resource_group(fragment) if contains(input.deployment.resourceGroupName, fragment)`
    // into `contains(input.deployment.resourceGroupName, "prod")` so a
    // consumer can render the body without leaking helper parameter names or
    // the rule head into user-facing output.
    let substitutions = extract_helper_arg_substitutions(outer_pc, helper_rule_index, program);
    for cond in inner.iter_mut() {
        cond.text = rewrite_helper_body_text(&cond.text, &substitutions);
    }

    // Drop no-op inner entries. Helper invocation emits per-arg
    // register-binding Move outcomes which surface as `kind: "unknown"` with
    // empty `text` — they represent internal wiring (arg → param register
    // move), not authorable predicates.
    inner.retain(|c| !(c.kind == "unknown" && c.text.is_empty()));

    (inner, false, Some(call))
}

/// Walk backward from `outer_pc` to locate the `FunctionCall`
/// instruction that invoked the helper. Mirrors `detect_helper_call_at_guard`:
/// the FunctionCall is either directly preceding the Guard (for `_helper(x)`),
/// or a few instructions before a `Not` (for `not _helper(x)`).
fn find_preceding_function_call_pc(outer_pc: usize, program: &Program) -> Option<usize> {
    if outer_pc == 0 {
        return None;
    }
    let prev_pc = outer_pc.saturating_sub(1);
    let prev = program.instructions.get(prev_pc)?;
    match *prev {
        Instruction::FunctionCall { .. } => Some(prev_pc),
        Instruction::Not { .. } => {
            const LOOKBACK: usize = 8;
            let start = prev_pc.saturating_sub(LOOKBACK);
            let mut cur = prev_pc;
            while cur > start {
                cur = cur.saturating_sub(1);
                if let Some(Instruction::FunctionCall { .. }) = program.instructions.get(cur) {
                    return Some(cur);
                }
            }
            None
        }
        _ => None,
    }
}

/// Build `(param_name, arg_source_literal)` pairs so
/// [`rewrite_helper_body_text`] can substitute the helper's parameter names
/// with the caller's literal argument values. Only literal arguments
/// (`Load { dest, literal_idx }` writing to the arg register) are recovered;
/// dynamic-value args leave the parameter name unsubstituted (the body text
/// stays as-is for that identifier).
fn extract_helper_arg_substitutions(
    outer_pc: usize,
    helper_rule_index: u16,
    program: &Program,
) -> Vec<(String, String)> {
    let Some(fn_call_pc) = find_preceding_function_call_pc(outer_pc, program) else {
        return Vec::new();
    };
    let Some(&Instruction::FunctionCall { params_index }) = program.instructions.get(fn_call_pc)
    else {
        return Vec::new();
    };
    let Some(params) = program
        .instruction_data
        .function_call_params
        .get(usize::from(params_index))
    else {
        return Vec::new();
    };
    let Some(rule_info) = program.rule_infos.get(usize::from(helper_rule_index)) else {
        return Vec::new();
    };
    let Some(function_info) = &rule_info.function_info else {
        return Vec::new();
    };
    let arg_registers = params.arg_registers();
    let mut substitutions: Vec<(String, String)> = Vec::new();
    for (i, param_name) in function_info.param_names.iter().enumerate() {
        let Some(&arg_reg) = arg_registers.get(i) else {
            break;
        };
        if let Some(literal_str) = find_literal_load(fn_call_pc, arg_reg, program) {
            substitutions.push((param_name.clone(), literal_str));
        }
    }
    substitutions
}

/// Walk backward from `pc` (exclusive) within a bounded window,
/// looking for a `Load { dest, literal_idx }` that wrote to `target_reg`.
/// Returns the loaded value formatted as its Rego source literal (via
/// [`format_value`]) when found. Returns `None` when the arg was not
/// populated by a simple literal load (e.g. dynamic value, chained index,
/// arithmetic result) — in which case the caller leaves the parameter
/// name unsubstituted in the body text.
fn find_literal_load(pc: usize, target_reg: u8, program: &Program) -> Option<String> {
    const LOOKBACK: usize = 32;
    let start = pc.saturating_sub(LOOKBACK);
    let mut cur = pc;
    while cur > start {
        cur = cur.saturating_sub(1);
        let instr = program.instructions.get(cur)?;
        if let Instruction::Load { dest, literal_idx } = *instr {
            if dest == target_reg {
                let literal = program.literals.get(usize::from(literal_idx))?;
                return Some(format_value(literal));
            }
        }
    }
    None
}

/// Rewrite a helper inner condition's raw source text so it renders
/// as just the body expression with parameter names substituted. Two passes:
///
/// 1. Slice past the first ` if ` boundary (the Rego rule-head/body separator)
///    to drop the helper rule declaration prefix. Absent ` if ` means the
///    text was already body-only (e.g. 0-arg helper's Guard on an inline
///    expression) and no slicing occurs.
/// 2. For each `(param, literal)` pair, do a word-boundary substitution of
///    `param` → `literal` throughout the body. Only identifier-token matches
///    are replaced; substrings inside longer identifiers or other tokens are
///    left alone.
fn rewrite_helper_body_text(text: &str, substitutions: &[(String, String)]) -> String {
    const SEPARATOR: &str = " if ";
    let body = text
        .find(SEPARATOR)
        .and_then(|pos| pos.checked_add(SEPARATOR.len()))
        .and_then(|body_start| text.get(body_start..))
        .unwrap_or(text);
    let mut current = body.to_string();
    for (param, replacement) in substitutions {
        current = substitute_identifier(&current, param, replacement);
    }
    current
}

/// Word-boundary-aware substitution used to swap helper parameter
/// names for caller-supplied argument literals in helper body text. Boundary
/// characters are ASCII identifier characters (`[A-Za-z0-9_]`); other bytes,
/// including all non-ASCII, count as a boundary. Rego parameter names are
/// ASCII identifiers by grammar, so a byte-level check is sound here.
fn substitute_identifier(text: &str, pattern: &str, replacement: &str) -> String {
    if pattern.is_empty() {
        return text.to_string();
    }
    let mut out = String::with_capacity(text.len());
    let mut cursor = 0;
    while cursor < text.len() {
        match text[cursor..].find(pattern) {
            Some(rel) => {
                let start = cursor.saturating_add(rel);
                let end = start.saturating_add(pattern.len());
                out.push_str(&text[cursor..start]);
                let left_ok = start == 0
                    || !text[..start]
                        .chars()
                        .next_back()
                        .is_some_and(is_identifier_char);
                let right_ok = end == text.len()
                    || !text[end..].chars().next().is_some_and(is_identifier_char);
                if left_ok && right_ok {
                    out.push_str(replacement);
                } else {
                    // Preserve the false match verbatim; don't rescan into it.
                    out.push_str(&text[start..end]);
                }
                cursor = end;
            }
            None => {
                out.push_str(&text[cursor..]);
                break;
            }
        }
    }
    out
}

/// ASCII identifier character predicate. Rego identifiers are
/// `[A-Za-z_][A-Za-z0-9_]*` per grammar, so non-ASCII characters are always
/// boundaries.
const fn is_identifier_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// Whether the guard at `guard_pc`, whose outcome is `outcome_idx`, held only
/// because the `not` just before it was assumed to hold. The `Not` records its
/// `NegationHolds` assumption immediately before the guard records its
/// outcome, so the two are linked by the outcome count.
///
/// The engine also records an empty `NegationHolds` whenever the negated
/// value is undefined for any reason; partial evaluation drops those as
/// trivial wrappers. Like it, only a negation whose own scope recorded an
/// assumption counts. The guard's outcome is judged on its own, so an
/// assumption orphaned later because the enclosing definition failed still
/// counts.
fn guard_holds_by_assumed_negation(
    guard_pc: usize,
    outcome_idx: usize,
    program: &Program,
    trace: &EvaluationTrace,
) -> bool {
    let Some(not_pc) = guard_pc.checked_sub(1) else {
        return false;
    };
    if !matches!(
        program.instructions.get(not_pc),
        Some(Instruction::Not { .. })
    ) {
        return false;
    }
    let Ok(recorded) = u32::try_from(outcome_idx) else {
        return false;
    };
    // Assumptions are appended in order, so `conditions_recorded` never
    // decreases: binary-search to the ones recorded just before this guard.
    let start = trace
        .assumptions
        .partition_point(|assumption| assumption.conditions_recorded < recorded);
    trace
        .assumptions
        .get(start..)
        .unwrap_or_default()
        .iter()
        .enumerate()
        .take_while(|(_, assumption)| assumption.conditions_recorded == recorded)
        .filter(|(_, assumption)| {
            assumption.kind == AssumptionKind::NegationHolds
                && usize::try_from(assumption.pc).is_ok_and(|pc| pc == not_pc)
        })
        .any(|(offset, _)| negation_is_live(start.saturating_add(offset), trace))
}

/// Whether the `NegationHolds` at `index` owns a scope that recorded an
/// assumption, as partial evaluation decides when it keeps or drops the
/// negation: any assumption but a nested negation, which counts only when its
/// own scope did.
///
/// Partial evaluation skips orphaned assumptions, so an orphaned inner
/// assumption counts only when the negation itself was orphaned with it (the
/// enclosing definition failed after the guard); otherwise the engine decided
/// the negation concretely.
///
/// A negation's body is recorded before the negation, so one forward pass
/// over the earlier assumptions settles every nested scope, at any depth.
fn negation_is_live(index: usize, trace: &EvaluationTrace) -> bool {
    let Some(negation) = trace.assumptions.get(index) else {
        return false;
    };
    let Some(scope) = negation.owned_negation_scope_id else {
        return false;
    };
    // Scope ids increase over time, and the body of scope `scope` is recorded
    // just before its negation: the window is the run of assumptions back to
    // the first one outside `scope` and the scopes nested in it.
    let earlier = trace.assumptions.get(..index).unwrap_or_default();
    let body_start = earlier
        .iter()
        .rposition(|inner| inner.negation_scope_id.is_none_or(|id| id < scope))
        .map_or(0, |position| position.saturating_add(1));
    // Scopes holding a live non-orphaned assumption, and a live assumption
    // of either kind.
    let mut live_strict = alloc::collections::BTreeSet::new();
    let mut live_any = alloc::collections::BTreeSet::new();
    for inner in earlier.get(body_start..).unwrap_or_default() {
        let Some(inner_scope) = inner.negation_scope_id else {
            continue;
        };
        let live = inner.kind != AssumptionKind::NegationHolds
            || inner.owned_negation_scope_id.is_some_and(|owned| {
                if inner.orphaned {
                    live_any.contains(&owned)
                } else {
                    live_strict.contains(&owned)
                }
            });
        if live {
            live_any.insert(inner_scope);
            if !inner.orphaned {
                live_strict.insert(inner_scope);
            }
        }
    }
    if negation.orphaned {
        live_any.contains(&scope)
    } else {
        live_strict.contains(&scope)
    }
}

/// A complete rule or a function: a truthiness check of its result depends on
/// its value, unlike a partial set or object, which is always truthy.
fn is_single_valued_rule(rule_index: u16, program: &Program) -> bool {
    program
        .rule_infos
        .get(usize::from(rule_index))
        .is_some_and(|info| {
            matches!(info.rule_type, RuleType::Complete) || info.function_info.is_some()
        })
}

/// Whether the call to `call`'s helper that finished just before the
/// condition at `outer_outcome_idx` depended on an assumption at any depth,
/// as the VM recorded on its summary. In partial evaluation `not` treats such
/// a result as unknown, so the guard can hold although the helper held.
/// A rule with no definitions (only a default) records no summary and never
/// depends on an assumption. Otherwise fails closed when the summary cannot
/// be found.
fn call_depends_on_assumption(
    call: HelperCall,
    outer_outcome_idx: usize,
    program: &Program,
    trace: &EvaluationTrace,
) -> bool {
    if trace.assumptions.is_empty()
        || program
            .rule_infos
            .get(usize::from(call.rule_index))
            .is_some_and(|info| info.definitions.is_empty())
    {
        return false;
    }
    trace
        .rule_outcomes
        .iter()
        .rev()
        .find(|outcome| {
            outcome.is_summary
                && outcome.rule_index == call.rule_index
                && usize::try_from(outcome.conditions_recorded)
                    .is_ok_and(|recorded| recorded <= outer_outcome_idx)
        })
        .is_none_or(|outcome| outcome.assumption_dependent)
}

/// Derive the outer truthiness condition's `left.provenance` from the
/// last failed helper inner condition. When the outer already has a
/// provenance we don't overwrite; when it has an operand but no provenance,
/// we augment it; when it has no operand at all, we leave it alone (a fully
/// missing `left` on the outer is the engine's signal that the operand isn't
/// meaningfully attributable to a single value).
///
/// Callers apply it only when the helper definitely returned falsy. Known
/// limitation: a definition that holds but returns `false` is falsy too, and
/// an earlier definition's failed condition can then still be borrowed;
/// telling the producing attempt apart needs attempt boundaries (RG-11).
fn derive_left_provenance_from_helper(
    left: Option<OperandExplanation>,
    helper_conditions: &[ConditionExplanation],
) -> Option<OperandExplanation> {
    let existing = left?;
    if existing.provenance.is_some() {
        return Some(existing);
    }
    // Find the last inner condition whose outcome is "failure" and whose
    // `left` carries a provenance. Iterating in reverse mirrors the fact that
    // a helper body short-circuits on its first failing condition -- the one
    // that actually determined the helper's Undefined/false return.
    let derived_provenance = helper_conditions.iter().rev().find_map(|inner| {
        if inner.outcome != "failure" {
            return None;
        }
        inner.left.as_ref().and_then(|op| op.provenance.clone())
    });
    match derived_provenance {
        Some(prov) => Some(OperandExplanation {
            value: existing.value,
            provenance: Some(prov),
            absent: existing.absent,
            truncated: existing.truncated,
            length: existing.length,
            redacted: existing.redacted,
            source_alias: existing.source_alias,
        }),
        None => Some(existing),
    }
}

/// Materialize the conditions of the emission at `emission_position` in
/// `trace.emission_outcomes`, whose window is the given condition range.
fn materialize_condition_window(
    condition_start_index: u32,
    condition_end_index: u32,
    outer_rule_index: u16,
    emission_position: usize,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<ConditionExplanation> {
    let relevant_outcomes = select_condition_outcomes_in_window(
        condition_start_index,
        condition_end_index,
        trace,
        settings,
    );

    // Filter out outcomes that belong to a helper rule scope: they are
    // surfaced structurally under `helper_conditions[]` on the outer
    // truthiness record that invoked the helper, so keeping them as siblings
    // here would duplicate them.
    let outer_only: Vec<(usize, &ConditionOutcome)> = relevant_outcomes
        .into_iter()
        .filter(|(_, o)| o.rule_index == outer_rule_index)
        .collect();

    finalize_condition_explanations(
        materialize_condition_explanations_at_depth(
            outer_only,
            program,
            trace,
            settings,
            0,
            WitnessScope::BeforeEmission(emission_position),
        ),
        settings,
        true,
    )
}

fn finalize_condition_explanations(
    mut conditions: Vec<ConditionExplanation>,
    settings: &ExplanationSettings,
    dedupe_for_emissions: bool,
) -> Vec<ConditionExplanation> {
    if dedupe_for_emissions && settings.detail != ExplanationDetail::Full {
        conditions = dedupe_emission_conditions(conditions);
    }

    if settings.detail == ExplanationDetail::Compact {
        conditions = compact_condition_explanations(conditions);
    }

    conditions
}

fn compact_condition_explanations(
    conditions: Vec<ConditionExplanation>,
) -> Vec<ConditionExplanation> {
    if conditions.is_empty() {
        return conditions;
    }

    let last_index = conditions.len().saturating_sub(1);

    conditions
        .into_iter()
        .enumerate()
        .filter_map(|(index, mut condition)| {
            let keep = index == last_index
                || condition.outcome != "success"
                || condition.kind == "existence";

            if !keep {
                return None;
            }

            condition.text = compact_condition_text(&condition);
            condition.location = None;
            condition.left = None;
            condition.right = None;
            condition.witness = None;

            Some(condition)
        })
        .collect()
}

fn compact_condition_text(condition: &ConditionExplanation) -> String {
    let Some(witness) = condition.witness.as_ref() else {
        return condition.text.clone();
    };

    alloc::format!(
        "{} [{}]",
        condition.text,
        format_loop_witness_summary(witness)
    )
}

fn format_loop_witness_summary(witness: &LoopWitnessExplanation) -> String {
    let mut summary = alloc::format!(
        "loop: {}/{} matched",
        witness.success_count,
        witness.total_iterations
    );

    if let Some(sample) = format_loop_witness_sample(witness) {
        summary.push_str("; sample: ");
        summary.push_str(&sample);
    }

    summary
}

fn format_loop_witness_sample(witness: &LoopWitnessExplanation) -> Option<String> {
    match (&witness.sample_key, &witness.sample_value) {
        (Some(key), Some(value)) => Some(alloc::format!("{key} => {value}")),
        (Some(key), None) => Some(key.to_string()),
        (None, Some(value)) => Some(value.to_string()),
        (None, None) => None,
    }
}

fn dedupe_emission_conditions(conditions: Vec<ConditionExplanation>) -> Vec<ConditionExplanation> {
    let mut deduped: Vec<ConditionExplanation> = Vec::new();

    'outer: for condition in conditions {
        for existing in &deduped {
            if existing.text == condition.text
                && existing.outcome == condition.outcome
                && existing.kind == condition.kind
                && existing.operator == condition.operator
                && existing.scopes == condition.scopes
                && operands_match(existing.left.as_ref(), condition.left.as_ref())
                && operands_match(existing.right.as_ref(), condition.right.as_ref())
                && witnesses_match(existing.witness.as_ref(), condition.witness.as_ref())
            {
                continue 'outer;
            }
        }

        deduped.push(condition);
    }

    deduped
}

fn operands_match(left: Option<&OperandExplanation>, right: Option<&OperandExplanation>) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => {
            left.value == right.value
                && left.provenance == right.provenance
                && left.absent == right.absent
                && left.truncated == right.truncated
                && left.length == right.length
                && left.redacted == right.redacted
        }
        _ => false,
    }
}

fn witnesses_match(
    left: Option<&LoopWitnessExplanation>,
    right: Option<&LoopWitnessExplanation>,
) -> bool {
    match (left, right) {
        (None, None) => true,
        (Some(left), Some(right)) => {
            left.total_iterations == right.total_iterations
                && left.success_count == right.success_count
                && left.sample_key == right.sample_key
                && left.sample_value == right.sample_value
                && left.redacted == right.redacted
        }
        _ => false,
    }
}

fn materialize_condition_explanations(
    relevant_outcomes: Vec<(usize, &ConditionOutcome)>,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<ConditionExplanation> {
    materialize_condition_explanations_at_depth(
        relevant_outcomes,
        program,
        trace,
        settings,
        0,
        WitnessScope::Reported,
    )
}

/// Which completed loops may be summarized on a list of reported conditions.
#[derive(Clone, Copy)]
enum WitnessScope {
    /// A loop whose anchor (the last condition its own rule recorded while
    /// it ran) is among the reported ones.
    Reported,
    /// Such a loop that also belongs to the emission at this position of
    /// `trace.emission_outcomes`: it finished before the value was emitted,
    /// within a loop iteration still active at the emission (or at body
    /// level).
    BeforeEmission(usize),
}

/// Whether `stat` summarizes a loop accountable to `relevant_outcomes`
/// under `scope`.
fn witness_eligible(
    stat: &crate::evaluation_trace::LoopStat,
    relevant_outcomes: &[(usize, &ConditionOutcome)],
    trace: &EvaluationTrace,
    scope: WitnessScope,
) -> bool {
    let anchored = stat.anchor_condition_idx.is_some_and(|anchor| {
        relevant_outcomes
            .iter()
            .any(|(index, _)| u32::try_from(*index).is_ok_and(|index| index == anchor))
    });
    if !anchored {
        return false;
    }
    match scope {
        WitnessScope::Reported => true,
        WitnessScope::BeforeEmission(position) => {
            let finished_before =
                usize::try_from(stat.emissions_before_exit).is_ok_and(|count| count <= position);
            let enclosing_active = stat.enclosing_iteration.is_none_or(|iteration| {
                trace
                    .emission_outcomes
                    .get(position)
                    .is_some_and(|emission| emission.active_iterations.contains(&iteration))
            });
            finished_before && enclosing_active
        }
    }
}

/// Recursion-aware variant. Callers that materialize helper inner
/// bodies bump `depth` so we stop at `MAX_HELPER_DEPTH` to avoid unbounded
/// recursion on pathological policies (mutually-recursive helpers).
fn materialize_condition_explanations_at_depth(
    relevant_outcomes: Vec<(usize, &ConditionOutcome)>,
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
    depth: usize,
    witness_scope: WitnessScope,
) -> Vec<ConditionExplanation> {
    let mut conditions: Vec<ConditionExplanation> = Vec::new();

    for (outcome_idx, outcome) in &relevant_outcomes {
        let pc_usize: usize = outcome.pc.try_into().unwrap_or(0);

        let static_info = program
            .condition_infos
            .get(pc_usize)
            .and_then(Option::as_ref);

        let base_text = static_info.map(|i| i.text.clone()).unwrap_or_default();

        let kind = static_info
            .map(|i| format_condition_kind(&i.kind))
            .unwrap_or_else(|| "unknown".to_string());

        let operator = static_info
            .and_then(|i| i.operator.as_ref())
            .map(|op| op.to_string());

        let location = get_source_location(pc_usize, program);

        let (left, right) = materialize_operands(outcome, static_info, trace, settings);
        let witness = outcome
            .loop_stat_idx
            .and_then(|idx| trace.loop_stats.get(usize::from(idx)))
            .filter(|stat| witness_eligible(stat, &relevant_outcomes, trace, witness_scope))
            .map(|stat| loop_witness(stat, trace, settings));
        let binding_name = static_info.and_then(|i| i.binding_name.clone());
        let builtin_name = static_info.and_then(|i| i.builtin_name.clone());
        let negated = static_info.map(|i| i.negated).unwrap_or(false);
        let text = decorate_condition_text(base_text, static_info, left.as_ref());

        // For a truthiness condition whose backing Guard fires on a register
        // written by a rule call (`_helper(x)` or `not _helper(x)`), stitch
        // the helper's evaluated inner conditions as structural children.
        let (helper_conditions, helper_conditions_truncated, helper_call) =
            materialize_helper_conditions(
                pc_usize,
                *outcome_idx,
                outcome.rule_index,
                program,
                trace,
                settings,
                depth,
            );

        // A guard that held only through an assumption is assumed, not a
        // concrete success, following the engine's own decision: a check of a
        // single-valued call whose result depended on an unknown, or a `not`
        // that recorded a live `NegationHolds` (one that partial evaluation
        // turns into a residual).
        let held_by_assumption = outcome.passed
            && !outcome.assumed
            && (helper_call.is_some_and(|call| {
                is_single_valued_rule(call.rule_index, program)
                    && call_depends_on_assumption(call, *outcome_idx, program, trace)
            }) || guard_holds_by_assumed_negation(pc_usize, *outcome_idx, program, trace));
        let outcome_str = if outcome.assumed || held_by_assumption {
            "assumed"
        } else if outcome.passed {
            "success"
        } else {
            "failure"
        };

        // Derive outer `left.provenance` from the last failed helper inner
        // condition when the outer condition doesn't already carry one, but
        // only when the helper returned falsy: a helper that held may have
        // failed alternatives (earlier definitions or iterations) that did not
        // produce its result.
        let left = if helper_call.is_some_and(|call| {
            call.returned_falsy(outcome_str)
                && !call_depends_on_assumption(call, *outcome_idx, program, trace)
        }) {
            derive_left_provenance_from_helper(left, &helper_conditions)
        } else {
            left
        };
        let scopes = program
            .condition_scopes
            .get(pc_usize)
            .map(|scopes| scopes.iter().map(|scope| scope.as_str()).collect())
            .unwrap_or_default();
        let helper_rule = helper_call.and_then(|call| {
            program
                .rule_infos
                .get(usize::from(call.rule_index))
                .map(|info| info.name.clone())
        });

        conditions.push(ConditionExplanation {
            text,
            outcome: outcome_str.to_string(),
            location,
            kind,
            operator,
            left,
            right,
            witness,
            binding_name,
            builtin_name,
            negated,
            scopes,
            helper_rule,
            helper_conditions,
            helper_conditions_truncated,
        });
    }

    if conditions
        .iter()
        .all(|condition| condition.witness.is_none())
    {
        if let Some(witness) =
            materialize_reported_loop_witness(&relevant_outcomes, trace, settings, witness_scope)
        {
            if let Some(last) = conditions.last_mut() {
                last.witness = Some(witness);
            }
        }
    }

    conditions
}

/// The latest completed loop accountable to `relevant_outcomes` under `scope`.
/// There is no fallback: a loop that no reported condition anchors (or that
/// was still running when the value was emitted) is not summarized here.
fn materialize_reported_loop_witness(
    relevant_outcomes: &[(usize, &ConditionOutcome)],
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
    scope: WitnessScope,
) -> Option<LoopWitnessExplanation> {
    let stat = trace
        .loop_stats
        .iter()
        .rev()
        .find(|stat| witness_eligible(stat, relevant_outcomes, trace, scope))?;

    Some(loop_witness(stat, trace, settings))
}

/// Materialize a loop summary, redacting its sample like an operand under
/// `Redacted`: a sensitive collection path hides the key and the value, a
/// sensitive-named key hides the value, and nested secrets are sanitized.
fn loop_witness(
    stat: &crate::evaluation_trace::LoopStat,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> LoopWitnessExplanation {
    let mut sample_key = stat
        .sample_key
        .and_then(|idx| trace.get_value(idx))
        .cloned();
    let mut sample_value = stat
        .sample_value
        .and_then(|idx| trace.get_value(idx))
        .cloned();
    let mut redacted = false;

    if settings.value_mode == ValueMode::Redacted {
        let path_sensitive = should_redact_runtime_path(stat.collection_path.as_deref(), trace);
        let sample_path_sensitive = should_redact_runtime_path(stat.sample_path.as_deref(), trace);
        let key_sensitive = sample_key
            .as_ref()
            .and_then(|key| key.as_string().ok())
            .is_some_and(|key| is_sensitive_name(key));
        let recorded_key = sample_key
            .as_ref()
            .is_some_and(|key| is_sensitive_key(key, false, trace));
        let recorded_value = sample_value
            .as_ref()
            .is_some_and(|value| is_sensitive_key(value, stat.sample_path.is_some(), trace));
        let mut hide = |slot: &mut Option<Value>, whole: bool| {
            let Some(value) = slot.as_ref() else {
                return;
            };
            let replacement = sanitize_value(value, whole, trace);
            if let Some(replacement) = replacement {
                *slot = Some(replacement);
                redacted = true;
            }
        };
        hide(&mut sample_key, path_sensitive || recorded_key);
        hide(
            &mut sample_value,
            path_sensitive || sample_path_sensitive || key_sensitive || recorded_value,
        );
    }

    LoopWitnessExplanation {
        total_iterations: stat.total_iterations,
        success_count: stat.success_count,
        sample_key,
        sample_value,
        redacted,
    }
}
fn decorate_condition_text(
    base_text: String,
    static_info: Option<&crate::static_provenance::StaticConditionInfo>,
    left: Option<&OperandExplanation>,
) -> String {
    let Some(info) = static_info else {
        return base_text;
    };

    match info.kind {
        crate::static_provenance::ConditionKind::Existence => left
            .map(format_operand_for_text)
            .filter(|value| !value.is_empty())
            .map(|value| alloc::format!("{base_text} [matched: {value}]"))
            .unwrap_or(base_text),
        _ => base_text,
    }
}

fn format_operand_for_text(operand: &OperandExplanation) -> String {
    operand.provenance.as_ref().map_or_else(
        || operand.value.to_string(),
        |path| alloc::format!("{path}={}", operand.value),
    )
}

fn select_condition_outcomes<'a>(
    first_pc: u32,
    last_pc: u32,
    trace: &'a EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<(usize, &'a ConditionOutcome)> {
    let outcomes: Vec<(usize, &ConditionOutcome)> = trace
        .condition_outcomes
        .iter()
        .enumerate()
        .filter(|outcome| outcome.1.pc >= first_pc && outcome.1.pc <= last_pc)
        .collect();

    select_condition_outcomes_from_slice(outcomes, settings)
}

fn select_condition_outcomes_in_window<'a>(
    condition_start_index: u32,
    condition_end_index: u32,
    trace: &'a EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<(usize, &'a ConditionOutcome)> {
    let start_idx = usize::try_from(condition_start_index).unwrap_or(usize::MAX);
    let end_idx = usize::try_from(condition_end_index).unwrap_or(usize::MAX);

    let outcomes: Vec<(usize, &ConditionOutcome)> = trace
        .condition_outcomes
        .get(start_idx..end_idx)
        .unwrap_or(&[])
        .iter()
        .enumerate()
        .map(|(offset, outcome)| (start_idx.saturating_add(offset), outcome))
        .collect();

    select_condition_outcomes_from_slice(outcomes, settings)
}

fn select_condition_outcomes_from_slice<'a>(
    outcomes: Vec<(usize, &'a ConditionOutcome)>,
    settings: &ExplanationSettings,
) -> Vec<(usize, &'a ConditionOutcome)> {
    if settings.condition_mode == ConditionMode::AllContributing {
        return outcomes;
    }

    let mut selected: Vec<(usize, &ConditionOutcome)> = Vec::new();
    let mut seen_pcs: Vec<u32> = Vec::new();

    for outcome in outcomes.iter().rev().copied() {
        if seen_pcs.contains(&outcome.1.pc) {
            continue;
        }
        seen_pcs.push(outcome.1.pc);
        selected.push(outcome);
    }

    selected.reverse();
    selected
}

#[allow(clippy::option_if_let_else)]
fn materialize_operands(
    outcome: &ConditionOutcome,
    static_info: Option<&crate::static_provenance::StaticConditionInfo>,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> (Option<OperandExplanation>, Option<OperandExplanation>) {
    let actual = outcome
        .actual_value_idx
        .and_then(|idx| trace.get_value(idx))
        .cloned();
    let expected = outcome
        .expected_value_idx
        .and_then(|idx| trace.get_value(idx))
        .cloned();

    let (left_prov, right_prov) = static_info
        .and_then(|i| i.operands.as_ref())
        .map(|ops| (ops.left_provenance.as_ref(), ops.right_provenance.as_ref()))
        .unwrap_or((None, None));

    let left_runtime_path = outcome.actual_path.as_deref();
    let right_runtime_path = outcome.expected_path.as_deref();

    let redact = settings.value_mode == ValueMode::Redacted;

    let left_output_path =
        operand_provenance_for_output(left_runtime_path, left_prov, outcome, trace);
    let right_output_path =
        operand_provenance_for_output(right_runtime_path, right_prov, outcome, trace);

    // The first sensitive segment of each output path, found once and used
    // both to redact the value and to mask the keys beneath it.
    let first_sensitive = |path: Option<&String>| {
        path.filter(|_| redact)
            .and_then(|path| sensitive_segment(path, trace))
    };
    let left_first = first_sensitive(left_output_path.as_ref());
    let right_first = first_sensitive(right_output_path.as_ref());
    let left_sensitive = redact
        && if left_output_path.is_some() {
            left_first.is_some()
        } else {
            should_redact_path(left_prov)
        };
    let right_sensitive = redact
        && if right_output_path.is_some() {
            right_first.is_some()
        } else {
            should_redact_path(right_prov)
        };
    // Keys beneath a sensitive segment of a runtime path are secret too.
    let mask = |path: Option<String>, first: Option<usize>, runtime: bool| match (path, first) {
        (Some(path), Some(first)) if runtime => {
            Some(mask_runtime_path_from(&path, first).unwrap_or(path))
        }
        (path, _) => path,
    };
    let left_output_path = mask(left_output_path, left_first, left_runtime_path.is_some());
    let right_output_path = mask(right_output_path, right_first, right_runtime_path.is_some());
    // In a two-operand condition the operands are related (equal, ordered, or
    // container/member), so a harmless-looking side can reveal the sensitive
    // one. Redact both when either is sensitive, and sanitize nested secrets.
    // The shape comes from static metadata, not capture success: if the trace's
    // value capacity drops one operand, the survivor must still be sanitized.
    let paired = (actual.is_some() && expected.is_some())
        || static_info.is_some_and(|i| i.operator.is_some() || i.builtin_name.is_some());

    // Two-operand conditions can carry whole collections (`x in c`). Truncate
    // first so report size and the redaction walk are both bounded; then redact
    // what will actually be emitted.
    let left_sensitive = left_sensitive
        || (redact
            && actual
                .as_ref()
                .is_some_and(|v| is_sensitive_key(v, left_runtime_path.is_some(), trace)));
    let right_sensitive = right_sensitive
        || (redact
            && expected
                .as_ref()
                .is_some_and(|v| is_sensitive_key(v, right_runtime_path.is_some(), trace)));
    let shared = paired && (left_sensitive || right_sensitive);
    let prepare_operand = |v: Value, sensitive: bool| -> (Value, bool, bool, Option<usize>) {
        if sensitive || shared {
            return (Value::from("<redacted>"), true, false, None);
        }
        let (v, length) = if paired {
            match truncate_operand(&v) {
                Some((kept, length)) => (kept, Some(length)),
                None => (v, None),
            }
        } else {
            (v, None)
        };
        // Every reported value is sanitized, including single operands
        // (whole-object bindings, existence guards) that carry a nested secret
        // under a harmless path.
        if redact {
            if let Some(sanitized) = redact_nested_secrets_cached(&v, trace) {
                return (sanitized, true, length.is_some(), length);
            }
        }
        (v, false, length.is_some(), length)
    };

    let left = actual.map(|v| {
        let (value, redacted, truncated, length) = prepare_operand(v, left_sensitive);
        OperandExplanation {
            value,
            provenance: left_output_path.clone(),
            absent: outcome.actual_absent,
            truncated,
            length,
            redacted,
            source_alias: left_prov
                .and_then(|p| p.source_alias.as_deref())
                .map(str::to_string),
        }
    });

    let right = expected.map(|v| {
        let (value, redacted, truncated, length) = prepare_operand(v, right_sensitive);
        OperandExplanation {
            value,
            provenance: right_output_path.clone(),
            absent: false,
            truncated,
            length,
            redacted,
            source_alias: right_prov
                .and_then(|p| p.source_alias.as_deref())
                .map(str::to_string),
        }
    });

    (left, right)
}

/// Under `Redacted`, an assumed value is hidden whole when either the assumed
/// input path or the value's own provenance is sensitive, and otherwise has
/// its nested secrets sanitized, like the operands of a condition.
fn materialize_assumptions(
    program: &Program,
    trace: &EvaluationTrace,
    settings: &ExplanationSettings,
) -> Vec<AssumptionRecord> {
    trace
        .assumptions
        .iter()
        .map(|a| {
            let pc_usize: usize = a.pc.try_into().unwrap_or(0);
            let location = get_source_location(pc_usize, program);
            let kind_str = match a.kind {
                AssumptionKind::Exists => "exists",
                AssumptionKind::ConditionHolds => "condition_holds",
                AssumptionKind::CollectionExists => "collection_exists",
                AssumptionKind::NegationHolds => "negation_holds",
            };
            let redact = settings.value_mode == ValueMode::Redacted;
            let mut redacted = false;
            let assumed_value = a.assumed_value.as_ref().map(|value| {
                if !redact {
                    return value.clone();
                }
                let sensitive = should_redact_runtime_path(Some(&a.input_path), trace)
                    || should_redact_runtime_path(a.assumed_value_path.as_deref(), trace)
                    || is_sensitive_key(value, a.assumed_value_path.is_some(), trace);
                let sanitized = sanitize_value(value, sensitive, trace);
                redacted = sanitized.is_some();
                sanitized.unwrap_or_else(|| value.clone())
            });
            let masked_path = redact
                .then(|| mask_runtime_path(&a.input_path, trace))
                .flatten();
            // The condition text can quote the path (`collection at <path>
            // exists`), so it is masked the same way.
            let assumed_holds = match masked_path {
                Some(ref masked) if !a.input_path.is_empty() => {
                    a.condition_text.replace(a.input_path.as_str(), masked)
                }
                _ => a.condition_text.clone(),
            };
            let input_path = masked_path.unwrap_or_else(|| a.input_path.clone());
            AssumptionRecord {
                kind: kind_str.to_string(),
                input_path,
                redacted,
                assumed_holds,
                operator: a.operator.clone(),
                assumed_value,
                location,
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn get_source_location(pc: usize, program: &Program) -> Option<SourceLocation> {
    let span = program.instruction_spans.get(pc)?.as_ref()?;
    let file_name = program
        .sources
        .get(span.source_index)
        .map(|s| s.name.clone())
        .unwrap_or_default();
    Some(SourceLocation {
        file: file_name,
        row: span.line,
        col: span.column,
    })
}

fn find_rule_return_pc(start_pc: usize, program: &Program) -> u32 {
    let mut pc = start_pc;
    while pc < program.instructions.len() {
        if matches!(
            program.instructions.get(pc),
            Some(crate::rvm::Instruction::RuleReturn {})
        ) {
            return u32::try_from(pc).unwrap_or(u32::MAX);
        }
        pc = pc.saturating_add(1);
    }
    u32::try_from(program.instructions.len().saturating_sub(1)).unwrap_or(u32::MAX)
}

fn format_condition_kind(kind: &crate::static_provenance::ConditionKind) -> String {
    use crate::static_provenance::ConditionKind;
    match *kind {
        ConditionKind::Comparison => "comparison",
        ConditionKind::Membership => "membership",
        ConditionKind::Truthiness => "truthiness",
        ConditionKind::Existence => "existence",
        ConditionKind::EqualityAssertion => "equality_assertion",
        ConditionKind::Binding => "binding",
        ConditionKind::Builtin => "builtin",
    }
    .to_string()
}

#[cfg(all(test, feature = "explanations"))]
#[allow(clippy::indexing_slicing, clippy::unwrap_used)]
mod tests {
    use alloc::vec;
    use alloc::vec::Vec;

    use super::{
        dedupe_emission_conditions, materialize, materialize_condition_explanations,
        materialize_conditions, materialize_rule_emissions, ConditionExplanation,
        OperandExplanation,
    };
    use crate::evaluation_trace::{
        AssumptionKind, ConditionMode, EvaluationTrace, ExplanationDetail, ExplanationScope,
        ExplanationSettings, ValueMode,
    };
    use crate::rvm::program::{Program, RuleInfo, RuleType, SourceFile, SpanInfo};
    use crate::static_provenance::{ConditionKind, StaticConditionInfo};
    use crate::{value::Value, Rc};

    fn settings(condition_mode: ConditionMode) -> ExplanationSettings {
        ExplanationSettings {
            enabled: true,
            value_mode: ValueMode::Redacted,
            condition_mode,
            scope: ExplanationScope::AllEmissions,
            detail: ExplanationDetail::Standard,
            emission_index: None,
            emission_value: None,
            assume_unknown_input: false,
            eval_mode: crate::evaluation_trace::EvaluationMode::Causality,
            unknowns: vec![alloc::string::String::from("input")],
            max_derivations: 1,
        }
    }

    fn settings_with_detail(
        condition_mode: ConditionMode,
        detail: ExplanationDetail,
    ) -> ExplanationSettings {
        ExplanationSettings {
            detail,
            ..settings(condition_mode)
        }
    }

    #[test]
    fn primary_only_keeps_last_outcome_per_condition_site() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "a\nb\nc\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 1)),
            Some(SpanInfo::new(0, 2, 1, 1)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "cond one".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "cond two".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(1, false, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);

        let conditions = materialize_conditions(
            1,
            2,
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(conditions.len(), 2);
        assert_eq!(
            conditions.first().map(|c| c.text.as_str()),
            Some("cond one")
        );
        assert_eq!(
            conditions.first().map(|c| c.outcome.as_str()),
            Some("failure")
        );
        assert_eq!(conditions.get(1).map(|c| c.text.as_str()), Some("cond two"));
        assert_eq!(
            conditions.get(1).map(|c| c.outcome.as_str()),
            Some("success")
        );
    }

    #[test]
    fn all_contributing_keeps_all_outcomes() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "a\nb\n".into()));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 1))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "cond".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(1, false, false, None, None, None, None, 0);

        let conditions = materialize_conditions(
            1,
            1,
            &program,
            &trace,
            &settings(ConditionMode::AllContributing),
        );

        assert_eq!(conditions.len(), 2);
    }

    #[test]
    fn partial_set_rule_materializes_per_emission_conditions() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "first\nsecond\nsecond\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 6)),
            Some(SpanInfo::new(0, 3, 1, 6)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 0, 3, Value::from("violation a"), Vec::new());
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"), Vec::new());
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"), Vec::new());

        let emissions = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(emissions.len(), 2);
        assert_eq!(emissions[0].index, 0);
        assert_eq!(
            emissions.first().map(|emission| emission.result.clone()),
            Some(Value::from("violation a"))
        );
        assert_eq!(
            emissions.first().map(|emission| emission.conditions.len()),
            Some(2)
        );
        assert_eq!(
            emissions.get(1).map(|emission| emission.result.clone()),
            Some(Value::from("violation b"))
        );
        assert_eq!(emissions[1].index, 1);
        assert_eq!(
            emissions.get(1).map(|emission| emission.conditions.len()),
            Some(2)
        );
    }

    #[test]
    fn partial_set_rule_can_select_single_emission_by_index() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "first\nsecond\nsecond\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 6)),
            Some(SpanInfo::new(0, 3, 1, 6)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 0, 3, Value::from("violation a"), Vec::new());
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"), Vec::new());

        let emissions = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &ExplanationSettings {
                emission_index: Some(1),
                scope: ExplanationScope::SingleEmission,
                ..settings(ConditionMode::PrimaryOnly)
            },
        );

        assert_eq!(emissions.len(), 1);
        assert_eq!(emissions[0].index, 1);
        assert_eq!(emissions[0].result, Value::from("violation b"));
        assert_eq!(emissions[0].conditions.len(), 2);
    }

    #[test]
    fn partial_set_rule_can_select_single_emission_by_value() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "first\nsecond\nsecond\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 6)),
            Some(SpanInfo::new(0, 3, 1, 6)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "second".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 0, 3, Value::from("violation a"), Vec::new());
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_condition(3, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 3, 6, Value::from("violation b"), Vec::new());

        let emissions = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &ExplanationSettings {
                scope: ExplanationScope::SingleEmission,
                emission_value: Some(Value::from("violation a")),
                ..settings(ConditionMode::PrimaryOnly)
            },
        );

        assert_eq!(emissions.len(), 1);
        assert_eq!(emissions[0].index, 0);
        assert_eq!(emissions[0].result, Value::from("violation a"));
        assert_eq!(emissions[0].conditions.len(), 2);
    }

    #[test]
    fn standard_detail_dedupes_emission_conditions_but_full_keeps_all() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "dup\ndup\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 3)),
            Some(SpanInfo::new(0, 2, 1, 3)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "dup".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "dup".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info.clone());

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(2, true, false, None, None, None, None, 0);
        trace.record_emission(0, 0, 0, 2, Value::from("violation a"), Vec::new());

        let standard = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::AllContributing, ExplanationDetail::Standard),
        );
        let full = materialize_rule_emissions(
            0,
            &rule_info,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::AllContributing, ExplanationDetail::Full),
        );

        assert_eq!(standard.len(), 1);
        assert_eq!(standard[0].conditions.len(), 1);
        assert_eq!(full.len(), 1);
        assert_eq!(full[0].conditions.len(), 2);
    }

    #[test]
    fn compact_detail_inlines_witness_and_last_condition_but_strips_operands() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "helper\nsome item in coll\nfinal\n".into(),
        ));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 6)),
            Some(SpanInfo::new(0, 2, 1, 17)),
            Some(SpanInfo::new(0, 3, 1, 5)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "helper".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "some item in coll".into(),
                kind: ConditionKind::Existence,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "final".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_condition(
            2,
            true,
            false,
            Some(Value::from("match-a")),
            None,
            None,
            None,
            0,
        );
        trace.attach_loop_stat_to_last_condition(
            2,
            3,
            2,
            Some(Value::from(1_u64)),
            Some(Value::from("match-a")),
        );
        trace.record_condition(3, true, false, None, None, None, None, 0);

        let conditions = materialize_conditions(
            1,
            3,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::AllContributing, ExplanationDetail::Compact),
        );

        assert_eq!(conditions.len(), 2);
        assert_eq!(
            conditions[0].text,
            "some item in coll [matched: \"match-a\"] [loop: 2/3 matched; sample: 1 => \"match-a\"]"
        );
        assert_eq!(conditions[0].kind, "existence");
        assert!(conditions[0].left.is_none());
        assert!(conditions[0].right.is_none());
        assert!(conditions[0].location.is_none());
        assert!(conditions[0].witness.is_none());
        assert_eq!(conditions[1].text, "final");
        assert!(conditions[1].left.is_none());
        assert!(conditions[1].location.is_none());
    }

    #[test]
    fn standard_detail_keeps_structured_loop_witness() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "every item in input.list { item > 0 }\n".into(),
        ));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 34))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "every item in input.list { item > 0 }".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, Some(Value::Bool(true)), None, None, None, 0);
        trace.attach_loop_stat_to_last_condition(
            1,
            3,
            2,
            Some(Value::from(1_u64)),
            Some(Value::from("match-a")),
        );

        let conditions = materialize_conditions(
            1,
            1,
            &program,
            &trace,
            &settings_with_detail(ConditionMode::PrimaryOnly, ExplanationDetail::Standard),
        );

        assert_eq!(conditions.len(), 1);
        assert_eq!(conditions[0].text, "every item in input.list { item > 0 }");
        let witness = conditions[0].witness.as_ref().unwrap();
        assert_eq!(witness.total_iterations, 3);
        assert_eq!(witness.success_count, 2);
        assert_eq!(witness.sample_key, Some(Value::from(1_u64)));
        assert_eq!(witness.sample_value, Some(Value::from("match-a")));
    }

    #[test]
    fn compact_detail_suppresses_partial_set_definition_scaffolding_and_assumptions() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "first\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 1, 1, 5)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "first".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            None,
        ];
        program.instructions = vec![
            crate::rvm::Instruction::LoadTrue { dest: 0 },
            crate::rvm::Instruction::LoadTrue { dest: 0 },
            crate::rvm::Instruction::RuleReturn {},
        ];
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info);

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, None, None, None, None, 0);
        trace.record_rule_outcome(0, 0, true, Some(Value::from("violation a")));
        trace.record_emission(0, 0, 0, 1, Value::from("violation a"), Vec::new());
        trace.record_assumption(
            AssumptionKind::ConditionHolds,
            "input.foo".into(),
            "input.foo == true".into(),
            1,
            Some("==".into()),
            Some(Value::Bool(true)),
            0,
            0,
            None,
            0,
            Vec::new(),
        );

        let report = materialize(
            &program,
            &trace,
            &settings_with_detail(ConditionMode::PrimaryOnly, ExplanationDetail::Compact),
            Value::from("violation a"),
        );

        assert_eq!(report.assumptions.len(), 0);
        assert_eq!(report.rules.len(), 1);
        assert_eq!(report.rules[0].emissions.len(), 1);
        assert_eq!(report.rules[0].definitions.len(), 0);
    }

    #[test]
    fn quantifier_condition_materializes_loop_witness_summary() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "every item in input.list { item > 0 }\n".into(),
        ));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 34))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "every item in input.list { item > 0 }".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, Some(Value::Bool(true)), None, None, None, 0);
        trace.attach_loop_stat_to_last_condition(
            1,
            3,
            2,
            Some(Value::from(1_u64)),
            Some(Value::from("match-a")),
        );

        let conditions = materialize_conditions(
            1,
            1,
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(conditions.len(), 1);
        let witness = conditions[0].witness.as_ref().unwrap();
        assert_eq!(witness.total_iterations, 3);
        assert_eq!(witness.success_count, 2);
        assert_eq!(witness.sample_key, Some(Value::from(1_u64)));
        assert_eq!(witness.sample_value, Some(Value::from("match-a")));
    }

    #[test]
    fn condition_loop_witness_obeys_the_emission_scope() {
        use super::{materialize_condition_explanations_at_depth, WitnessScope};
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "every item in input.list { item > 0 }\n".into(),
        ));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 34))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "every item in input.list { item > 0 }".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        // The value is emitted before the loop on its condition finishes.
        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, Some(Value::Bool(true)), None, None, None, 0);
        trace.record_emission(0, 0, 0, 1, Value::from("v"), Vec::new());
        trace.attach_loop_stat_to_last_condition(1, 3, 2, None, None);

        let witness_in = |scope| {
            materialize_condition_explanations_at_depth(
                trace.condition_outcomes.iter().enumerate().collect(),
                &program,
                &trace,
                &settings(ConditionMode::PrimaryOnly),
                0,
                scope,
            )[0]
            .witness
            .clone()
        };
        assert!(witness_in(WitnessScope::Reported).is_some());
        assert_eq!(witness_in(WitnessScope::BeforeEmission(0)), None);
    }

    #[test]
    fn fallback_loop_witness_attaches_to_last_selected_condition() {
        let mut program = Program::new();
        program
            .sources
            .push(SourceFile::new("test.rego".into(), "n > 1\nn < 3\n".into()));
        program.instruction_spans = vec![
            None,
            Some(SpanInfo::new(0, 1, 1, 5)),
            Some(SpanInfo::new(0, 2, 1, 5)),
        ];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "n > 1".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "n < 3".into(),
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(1, true, false, Some(Value::Bool(true)), None, None, None, 0);
        trace.record_condition(
            2,
            false,
            false,
            Some(Value::Bool(false)),
            None,
            None,
            None,
            0,
        );
        trace.record_loop(
            2,
            Some(1),
            3,
            1,
            Some(Value::from(1_u64)),
            Some(Value::from(2_u64)),
            None,
            None,
            None,
        );

        let conditions = materialize_conditions(
            1,
            2,
            &program,
            &trace,
            &settings(ConditionMode::AllContributing),
        );

        assert_eq!(conditions.len(), 2);
        assert!(conditions[0].witness.is_none());
        let witness = conditions[1].witness.as_ref().unwrap();
        assert_eq!(witness.total_iterations, 3);
        assert_eq!(witness.success_count, 1);
        assert_eq!(witness.sample_key, Some(Value::from(1_u64)));
        assert_eq!(witness.sample_value, Some(Value::from(2_u64)));
    }

    #[test]
    fn rule_summary_scope_suppresses_definitions_and_emissions() {
        let mut program = Program::new();
        let rule_info = RuleInfo::new(
            "data.test.violations".into(),
            RuleType::PartialSet,
            Rc::new(vec![vec![1]]),
            0,
            1,
        );
        program.rule_infos.push(rule_info);

        let mut trace = EvaluationTrace::new();
        trace.record_rule_outcome(0, 0, true, Some(Value::from("violation a")));
        trace.record_emission(0, 0, 0, 0, Value::from("violation a"), Vec::new());

        let report = materialize(
            &program,
            &trace,
            &ExplanationSettings {
                scope: ExplanationScope::RuleSummary,
                ..settings_with_detail(ConditionMode::PrimaryOnly, ExplanationDetail::Standard)
            },
            Value::from("violation a"),
        );

        assert_eq!(report.rules.len(), 1);
        assert_eq!(report.rules[0].emissions.len(), 0);
        assert_eq!(report.rules[0].definitions.len(), 0);
    }

    #[test]
    fn existence_condition_text_includes_matched_value() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "some item in coll\n".into(),
        ));
        program.instruction_spans = vec![None, Some(SpanInfo::new(0, 1, 1, 8))];
        program.condition_infos = vec![
            None,
            Some(StaticConditionInfo {
                checked_register: 0,
                checked_provenance: None,
                operands: None,
                text: "some item in coll".into(),
                kind: ConditionKind::Existence,
                operator: None,
                has_input_operand: false,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }),
        ];

        let mut trace = EvaluationTrace::new();
        trace.record_condition(
            1,
            true,
            false,
            Some(Value::from("match-a")),
            None,
            None,
            None,
            0,
        );

        let conditions = materialize_condition_explanations(
            trace.condition_outcomes.iter().enumerate().collect(),
            &program,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );

        assert_eq!(
            conditions.first().map(|condition| condition.text.as_str()),
            Some("some item in coll [matched: \"match-a\"]")
        );
    }

    #[test]
    fn sensitive_names_match_after_normalization_and_only_real_fragments() {
        use super::is_sensitive_name;
        for name in [
            "password",
            "adminPassword",
            "DB_PASSWORD",
            "api-key",
            "apiKey",
            "API_KEY",
            "clientSecret",
            "sasToken",
            "privateKey",
            "private_key",
            "connectionString",
            "secureValue",
            "protectedSettings",
            "storageAccountKey",
            "primary_key",
            "Ocp-Apim-Subscription-Key",
            "pwd",
            "pass phrase",
        ] {
            assert!(is_sensitive_name(name), "{name} should be sensitive");
        }
        // Names longer than the inline buffer take the allocating path.
        let long_prefix = "x".repeat(super::INLINE_NAME_BYTES + 6);
        assert!(is_sensitive_name(&alloc::format!("{long_prefix}Password")));
        assert!(is_sensitive_name(&alloc::format!(
            "{long_prefix}_storage_account_key"
        )));
        assert!(!is_sensitive_name(&alloc::format!("{long_prefix}Location")));
        for name in [
            "name",
            "location",
            "keyVaultId",
            "publicKey",
            "sku",
            "accessTier",
            "displayName",
            "value",
            "allowSharedKeyAccess",
            "primaryKeyType",
        ] {
            assert!(!is_sensitive_name(name), "{name} should not be sensitive");
        }
    }

    #[test]
    fn runtime_paths_are_checked_one_segment_at_a_time() {
        use super::should_redact_runtime_path;
        let trace = EvaluationTrace::new();
        let sensitive = |path: &str| should_redact_runtime_path(Some(path), &trace);
        assert!(sensitive("input.resource.properties.adminPassword"));
        assert!(sensitive("input.settings[\"connection-string\"][0]"));
        assert!(sensitive("input.api_key"));
        // A key-material suffix ends a segment, not necessarily the path.
        assert!(sensitive("input.accounts[0].primaryKey.value"));
        assert!(!sensitive("input.access.key"));
        assert!(!sensitive("input.resource.name"));
        // A quoted key is one segment even when it holds separators.
        assert!(!sensitive("input.x[\"pass.word\"]"));
        assert!(sensitive("input.x[\"a].password\"]"));
        assert!(!should_redact_runtime_path(None, &trace));
    }

    #[test]
    fn runtime_path_parser_follows_the_vm_grammar() {
        use super::parse_runtime_path;
        let keys = |path: &str| {
            parse_runtime_path(path).map(|segments| {
                segments
                    .into_iter()
                    .map(|segment| {
                        segment
                            .key
                            .map_or_else(|| "#".into(), |key| key.into_owned())
                    })
                    .collect::<Vec<_>>()
            })
        };
        let owned = |items: &[&str]| {
            Some(
                items
                    .iter()
                    .map(|s| alloc::string::String::from(*s))
                    .collect::<Vec<_>>(),
            )
        };
        assert_eq!(keys("input"), owned(&["input"]));
        assert_eq!(keys("input.a[0].b"), owned(&["input", "a", "#", "b"]));
        assert_eq!(
            keys("input.x[\"a.b\"][\"q\\\"]\"]"),
            owned(&["input", "x", "a.b", "q\"]"])
        );
        assert_eq!(
            keys("input.x[{\"k\": [1]}]"),
            owned(&["input", "x", "{\"k\": [1]}"])
        );
        // `IndexLiteral` writes any string key after a dot; numbers are indices.
        assert_eq!(
            keys("input.app-settings[-1.5]"),
            owned(&["input", "app-settings", "#"])
        );
        for malformed in [
            "",
            ".a",
            "input.",
            "input[",
            "input[\"a\"",
            "input..a",
            "input[1",
        ] {
            assert_eq!(keys(malformed), None, "{malformed:?}");
        }
    }

    #[test]
    fn keys_beneath_a_sensitive_segment_are_masked() {
        use super::mask_runtime_path;
        let trace = EvaluationTrace::new();
        assert_eq!(
            mask_runtime_path("input.tokens[\"opaque-42\"]", &trace).as_deref(),
            Some("input.tokens[\"<redacted>\"]")
        );
        assert_eq!(
            mask_runtime_path("input.secrets.prod[3].key", &trace).as_deref(),
            Some("input.secrets[\"<redacted>\"][3][\"<redacted>\"]")
        );
        // Nothing beneath the sensitive segment, or nothing sensitive.
        assert_eq!(
            mask_runtime_path("input.properties.adminPassword", &trace),
            None
        );
        assert_eq!(mask_runtime_path("input.regions[\"westus\"]", &trace), None);
        // An unparsable sensitive path is hidden whole.
        assert_eq!(
            mask_runtime_path("input.token[", &trace).as_deref(),
            Some("<redacted>")
        );
    }

    #[test]
    fn paths_the_vm_writes_for_non_identifier_fields_are_understood() {
        use super::{mask_runtime_path, should_redact_runtime_path};
        let mut trace = EvaluationTrace::new();
        // `IndexLiteral` writes `.field` for any string key.
        assert!(should_redact_runtime_path(Some("input.my-secret"), &trace));
        assert!(!should_redact_runtime_path(
            Some("input.app-settings.value"),
            &trace
        ));
        trace.record_sensitive_value_path("input.app-settings.value");
        assert!(should_redact_runtime_path(
            Some("input.app-settings.value"),
            &trace
        ));
        // A path that still fails to parse keeps its recorded pair prefix.
        trace.record_sensitive_value_path("input.odd.value");
        assert!(should_redact_runtime_path(
            Some("input.odd.value[\"unterminated"),
            &trace
        ));
        assert!(!should_redact_runtime_path(
            Some("input.odd.valueX[\"unterminated"),
            &trace
        ));
        // Once the record overflows, an unparsable path fails closed.
        let mut overflowed = EvaluationTrace::new();
        overflowed.sensitive_value_paths_overflowed = true;
        assert!(should_redact_runtime_path(
            Some("input.odd[.value"),
            &overflowed
        ));
        // A field holding `[` makes `IndexLiteral` write a path the parser
        // cannot read before the recorded prefix ends.
        trace.record_sensitive_value_path("input.we[ird.value");
        assert!(should_redact_runtime_path(
            Some("input.we[ird.value"),
            &trace
        ));
        assert!(!should_redact_runtime_path(
            Some("input.we[ird.valueX"),
            &trace
        ));
        // Compound keys beneath a sensitive segment are masked like string keys.
        let fresh = EvaluationTrace::new();
        assert_eq!(
            mask_runtime_path("input.tokens[[\"opaque-42\"]][0]", &fresh).as_deref(),
            Some("input.tokens[\"<redacted>\"][0]")
        );
    }

    #[test]
    fn assumption_text_masks_the_path_it_quotes() {
        use super::materialize_assumptions;
        let program = Program::new();
        let mut trace = EvaluationTrace::new();
        let path = "input.tokens[\"opaque-42\"].items";
        trace.record_assumption(
            AssumptionKind::CollectionExists,
            path.into(),
            alloc::format!("collection at {path} exists"),
            0,
            None,
            None,
            0,
            0,
            None,
            0,
            Vec::new(),
        );
        let redacted = ExplanationSettings {
            value_mode: ValueMode::Redacted,
            ..settings(ConditionMode::PrimaryOnly)
        };
        let records = materialize_assumptions(&program, &trace, &redacted);
        assert_eq!(
            records[0].input_path,
            "input.tokens[\"<redacted>\"][\"<redacted>\"]"
        );
        assert_eq!(
            records[0].assumed_holds,
            "collection at input.tokens[\"<redacted>\"][\"<redacted>\"] exists"
        );
        let full = ExplanationSettings {
            value_mode: ValueMode::Full,
            ..settings(ConditionMode::PrimaryOnly)
        };
        let full_records = materialize_assumptions(&program, &trace, &full);
        assert_eq!(
            full_records[0].assumed_holds,
            alloc::format!("collection at {path} exists")
        );
    }

    #[test]
    fn recorded_pair_values_are_sensitive_and_overflow_fails_closed() {
        use super::should_redact_runtime_path;
        let mut trace = EvaluationTrace::new();
        let pair = "input.appSettings[0].value";
        assert!(!should_redact_runtime_path(Some(pair), &trace));
        trace.record_sensitive_value_path(pair);
        assert!(should_redact_runtime_path(Some(pair), &trace));
        assert!(should_redact_runtime_path(
            Some("input.appSettings[0].value.inner"),
            &trace
        ));
        assert!(!should_redact_runtime_path(
            Some("input.appSettings[1].value"),
            &trace
        ));
        assert!(!should_redact_runtime_path(
            Some("input.appSettings[0].valueX"),
            &trace
        ));

        for i in 0..crate::evaluation_trace::MAX_SENSITIVE_VALUE_PATHS {
            trace.record_sensitive_value_path(&alloc::format!("input.p{i}.value"));
        }
        assert!(trace.sensitive_value_paths_overflowed);
        assert_eq!(
            trace.sensitive_value_paths.len(),
            crate::evaluation_trace::MAX_SENSITIVE_VALUE_PATHS
        );
        assert!(should_redact_runtime_path(
            Some("input.appSettings[9].value"),
            &trace
        ));
        assert!(!should_redact_runtime_path(
            Some("input.appSettings[9].name"),
            &trace
        ));
    }

    #[test]
    fn name_value_pairs_redact_the_value_of_a_sensitive_name() {
        use super::redact_nested_secrets;
        let parse = |s: &str| Value::from_json_str(s).unwrap();
        let settings = parse(
            r#"[{"name": "DB_PASSWORD", "value": "hunter2"},
                {"name": "REGION", "value": "westus"}]"#,
        );
        assert_eq!(
            redact_nested_secrets(&settings, 0),
            Some(parse(
                r#"[{"name": "DB_PASSWORD", "value": "<redacted>"},
                    {"name": "REGION", "value": "westus"}]"#
            ))
        );
        let harmless = parse(r#"[{"name": "REGION", "value": "westus"}]"#);
        assert_eq!(redact_nested_secrets(&harmless, 0), None);
        // Detection alone (no other secret in the value) must see the pair.
        assert!(super::contains_nested_secret(
            &parse(r#"{"name": "apiKey", "value": "k"}"#),
            0
        ));
        assert!(!super::contains_nested_secret(
            &parse(r#"{"name": "apiKey", "kind": "k"}"#),
            0
        ));
    }

    #[test]
    fn witnesses_match_distinguishes_redaction() {
        use super::{witnesses_match, LoopWitnessExplanation};
        let witness = |redacted| LoopWitnessExplanation {
            total_iterations: 2,
            success_count: 1,
            sample_key: Some(Value::from("k")),
            sample_value: Some(Value::from("<redacted>")),
            redacted,
        };
        assert!(witnesses_match(Some(&witness(true)), Some(&witness(true))));
        assert!(!witnesses_match(
            Some(&witness(true)),
            Some(&witness(false))
        ));
        assert!(witnesses_match(None, None));
        assert!(!witnesses_match(Some(&witness(false)), None));
    }

    #[test]
    fn nested_secret_cache_is_keyed_by_allocation_only() {
        use super::redact_nested_secrets_cached;
        let parse = |s: &str| Value::from_json_str(s).unwrap();
        let trace = EvaluationTrace::new();
        let secret = parse(r#"{"name": "a", "password": "p"}"#);
        let harmless = parse(r#"{"name": "a", "region": "w"}"#);
        let hidden = Some(parse(r#"{"name": "a", "password": "<redacted>"}"#));
        assert_eq!(redact_nested_secrets_cached(&secret, &trace), hidden);
        // A shared clone is the same allocation and hits the cache.
        assert_eq!(
            redact_nested_secrets_cached(&secret.clone(), &trace),
            hidden
        );
        assert_eq!(trace.nested_secret_cache.borrow().len(), 1);
        // A different allocation is walked on its own.
        assert_eq!(redact_nested_secrets_cached(&harmless, &trace), None);
        assert_eq!(trace.nested_secret_cache.borrow().len(), 2);
        // Scalars are never cached.
        assert_eq!(
            redact_nested_secrets_cached(&Value::from("p"), &trace),
            None
        );
        assert_eq!(trace.nested_secret_cache.borrow().len(), 2);
    }

    #[test]
    fn redact_nested_secrets_walks_containers_and_caps_depth() {
        use super::{redact_nested_secrets, MAX_REDACT_DEPTH};
        let parse = |s: &str| Value::from_json_str(s).unwrap();

        // Nothing sensitive: no copy is produced.
        assert!(redact_nested_secrets(&parse(r#"{"a":[1,{"b":"c"}]}"#), 0).is_none());
        assert!(redact_nested_secrets(&Value::from("password"), 0).is_none());

        // Sensitive keys at any depth, through arrays.
        let out = redact_nested_secrets(
            &parse(r#"{"name":"n","nested":[{"apiKey":"k"},{"ok":1}],"Password":"p"}"#),
            0,
        )
        .unwrap();
        assert_eq!(
            out,
            parse(
                r#"{"name":"n","nested":[{"apiKey":"<redacted>"},{"ok":1}],"Password":"<redacted>"}"#
            )
        );

        // Sets are walked too; non-string keys are not treated as names.
        let mut set = alloc::collections::BTreeSet::new();
        set.insert(parse(r#"{"token":"t"}"#));
        let set_out = redact_nested_secrets(&Value::from(set), 0).unwrap();
        assert!(!alloc::format!("{set_out}").contains("\"t\""), "{set_out}");
        let mut keyed = alloc::collections::BTreeMap::new();
        keyed.insert(Value::from(1), Value::from("secret-looking"));
        assert!(redact_nested_secrets(&Value::from(keyed), 0).is_none());

        // Beyond the depth cap any container fails closed.
        assert_eq!(
            redact_nested_secrets(&parse(r#"{"a":1}"#), MAX_REDACT_DEPTH),
            Some(Value::from("<redacted>"))
        );

        // A secret inside a compound key fails closed for the whole object.
        let mut inner = alloc::collections::BTreeMap::new();
        inner.insert(Value::from("password"), Value::from("hunter2"));
        let mut compound = alloc::collections::BTreeMap::new();
        compound.insert(Value::from(inner), Value::from(1));
        compound.insert(Value::from("ok"), Value::from(2));
        assert_eq!(
            redact_nested_secrets(&Value::from(compound), 0),
            Some(Value::from("<redacted>"))
        );
        assert!(redact_nested_secrets(&Value::from(1), MAX_REDACT_DEPTH).is_none());
    }

    #[test]
    fn paired_redaction_survives_a_dropped_partner_operand() {
        use crate::static_provenance::Operator;
        let comparison = StaticConditionInfo {
            checked_register: 0,
            checked_provenance: None,
            operands: None,
            text: "input.profile != {}".into(),
            kind: ConditionKind::Comparison,
            operator: Some(Operator::Ne),
            has_input_operand: true,
            binding_name: None,
            builtin_name: None,
            negated: false,
        };
        let secret = Value::from_json_str(r#"{"password":"hunter2","name":"n"}"#).unwrap();
        // Only `actual` is captured, as when the trace's value capacity is exhausted.
        let mut trace = EvaluationTrace::new();
        trace.record_condition(
            1,
            true,
            false,
            Some(secret),
            Some("input.profile".into()),
            None,
            None,
            0,
        );
        let outcome = trace.condition_outcomes.first().unwrap();
        let (left, right) = super::materialize_operands(
            outcome,
            Some(&comparison),
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );
        let left = left.unwrap();
        assert!(right.is_none());
        assert!(left.redacted);
        assert!(!alloc::format!("{}", left.value).contains("hunter2"));

        // A single operand is sanitized the same way (RG-R2).
        let (single, _) = super::materialize_operands(
            outcome,
            None,
            &trace,
            &settings(ConditionMode::PrimaryOnly),
        );
        let single = single.unwrap();
        assert!(single.redacted);
        assert!(!alloc::format!("{}", single.value).contains("hunter2"));

        // Control: Full value mode leaves it untouched.
        let mut full = settings(ConditionMode::PrimaryOnly);
        full.value_mode = ValueMode::Full;
        let (unredacted, _) = super::materialize_operands(outcome, None, &trace, &full);
        let unredacted = unredacted.unwrap();
        assert!(!unredacted.redacted);
        assert!(alloc::format!("{}", unredacted.value).contains("hunter2"));
    }

    #[test]
    fn operand_absence_is_distinct_and_omitted_when_false() {
        let defined = OperandExplanation {
            value: Value::Bool(true),
            provenance: Some("input.enabled".into()),
            absent: false,
            truncated: false,
            length: None,
            redacted: false,
            source_alias: None,
        };
        let mut absent = defined.clone();
        absent.absent = true;
        assert!(!super::operands_match(Some(&defined), Some(&absent)));
        assert!(super::operands_match(Some(&absent), Some(&absent)));
        assert!(serde_json::to_value(&defined)
            .unwrap()
            .get("absent")
            .is_none());
        assert_eq!(serde_json::to_value(&absent).unwrap()["absent"], true);
    }

    #[test]
    fn emission_dedup_keeps_distinct_witness_values() {
        let conditions = vec![
            ConditionExplanation {
                text: "some item in coll [matched: a]".into(),
                outcome: "success".into(),
                location: None,
                kind: "existence".into(),
                operator: None,
                left: Some(OperandExplanation {
                    value: Value::from("a"),
                    provenance: None,
                    absent: false,
                    truncated: false,
                    length: None,
                    redacted: false,
                    source_alias: None,
                }),
                right: None,
                witness: None,
                binding_name: None,
                builtin_name: None,
                negated: false,
                scopes: Vec::new(),
                helper_rule: None,
                helper_conditions: Vec::new(),
                helper_conditions_truncated: false,
            },
            ConditionExplanation {
                text: "some item in coll [matched: b]".into(),
                outcome: "success".into(),
                location: None,
                kind: "existence".into(),
                operator: None,
                left: Some(OperandExplanation {
                    value: Value::from("b"),
                    provenance: None,
                    absent: false,
                    truncated: false,
                    length: None,
                    redacted: false,
                    source_alias: None,
                }),
                right: None,
                witness: None,
                binding_name: None,
                builtin_name: None,
                negated: false,
                scopes: Vec::new(),
                helper_rule: None,
                helper_conditions: Vec::new(),
                helper_conditions_truncated: false,
            },
        ];

        let deduped = dedupe_emission_conditions(conditions);

        assert_eq!(deduped.len(), 2);
    }

    #[test]
    fn derivation_fingerprint_separates_nested_arrays_and_sets() {
        use super::{derivation_fingerprint, DerivationExplanation};

        fn two() -> Value {
            Value::from_json_str("2").unwrap()
        }
        fn nest(mut value: Value, depth: usize) -> Value {
            for _ in 0..depth {
                let mut array = Value::new_array();
                array.as_array_mut().unwrap().push(value);
                value = array;
            }
            value
        }
        fn array_of_two() -> Value {
            let mut array = Value::new_array();
            array.as_array_mut().unwrap().push(two());
            array
        }
        fn set_of_two() -> Value {
            let mut set = Value::new_set();
            set.as_set_mut().unwrap().insert(two());
            set
        }
        fn derivation(value: Value) -> DerivationExplanation {
            DerivationExplanation {
                definition_index: 0,
                conditions: vec![ConditionExplanation {
                    text: "i != null".into(),
                    outcome: "success".into(),
                    location: None,
                    kind: "comparison".into(),
                    operator: Some("!=".into()),
                    left: Some(OperandExplanation {
                        value,
                        provenance: None,
                        absent: false,
                        truncated: false,
                        length: None,
                        redacted: false,
                        source_alias: None,
                    }),
                    right: None,
                    witness: None,
                    binding_name: None,
                    builtin_name: None,
                    negated: false,
                    scopes: Vec::new(),
                    helper_rule: None,
                    helper_conditions: Vec::new(),
                    helper_conditions_truncated: false,
                }],
            }
        }

        // Equal numbers share a fingerprint whatever their representation.
        for (left, right) in [("2", "2.0"), ("1e2", "100")] {
            let left = Value::from_json_str(left).unwrap();
            let right = Value::from_json_str(right).unwrap();
            assert_eq!(left, right);
            assert_eq!(
                derivation_fingerprint(&derivation(left)),
                derivation_fingerprint(&derivation(right))
            );
        }

        for depth in [0_usize, 64, 300] {
            let array = derivation(nest(array_of_two(), depth));
            let set = derivation(nest(set_of_two(), depth));
            assert_eq!(
                serde_json::to_vec(&array).unwrap(),
                serde_json::to_vec(&set).unwrap(),
                "depth {depth}: JSON alone cannot tell them apart"
            );
            assert_ne!(
                derivation_fingerprint(&array),
                derivation_fingerprint(&set),
                "depth {depth}"
            );
            assert_eq!(
                derivation_fingerprint(&array),
                derivation_fingerprint(&derivation(nest(array_of_two(), depth))),
                "depth {depth}: equal derivations share a fingerprint"
            );
        }
    }
}
