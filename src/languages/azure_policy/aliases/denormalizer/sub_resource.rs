// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Sub-resource array re-wrapping during denormalization.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use crate::value::Object;
use crate::Value;

use super::super::obj_map::{
    is_element_envelope_field, obj_key_ci, set_nested, take_dotted_path_obj, val_str, ObjMap,
    ROOT_FIELDS,
};
use super::super::types::{ElementFields, ResolvedEntry};
use super::casing::restore_casing;

/// The denormalization state that re-wrapping reads.
pub struct Context<'a> {
    /// The resource type's resolved aliases, by lowercase short name.
    pub entries: &'a BTreeMap<String, ResolvedEntry>,
    /// The API version that selects each alias's ARM path.
    pub api_version: Option<&'a str>,
    /// What phases 2a, 2b and 2c wrote.
    pub writes: &'a Writes,
    /// Whether phase 2a put non-aliased keys at the ARM root.
    pub is_data_plane: bool,
    /// The key casing phases 2a and 2b restored.
    pub casing_map: &'a BTreeMap<String, String>,
    /// The aliased fields of each sub-resource array's elements.
    pub fields: &'a BTreeMap<String, ElementFields>,
}

/// The writes of phases 2a, 2b and 2c, in order.
#[derive(Debug, Default)]
pub struct Writes {
    /// The lowercase short names of the plain aliases phase 2b wrote.
    aliases: BTreeSet<String>,
    log: Vec<Write>,
}

/// One value written to the output.
#[derive(Debug)]
struct Write {
    /// Whether the write was at the ARM root rather than under `properties`.
    at_root: bool,
    /// The output keys written, as spelled there: keys differing only in
    /// case are distinct.
    keys: Vec<String>,
    /// The normalized name of the value, lowercase.
    source: String,
    /// The normalized key the value was read from, as it is spelled there.
    read: String,
}

/// The write that left a value in the output.
pub struct Origin {
    /// The value's normalized name: the write's source, followed by the keys
    /// below the write.
    pub name: String,
}

impl Writes {
    /// Record writing the value of normalized key `source`, read from the
    /// normalized key `read`, at the dotted path `keys`.
    pub fn record(&mut self, at_root: bool, keys: &str, source: &str, read: &str) {
        let keys = keys.split('.').map(String::from).collect();
        self.push(at_root, keys, source, read);
    }

    /// [`Self::record`] at the single, possibly dotted, key `key`.
    pub fn record_key(&mut self, at_root: bool, key: &str, source: &str, read: &str) {
        self.push(at_root, alloc::vec![String::from(key)], source, read);
    }

    /// Record phase 2b writing the plain alias `key`, read from the
    /// normalized key `read`, at `keys`.
    pub fn record_alias(&mut self, at_root: bool, keys: &str, key: &str, read: &str) {
        self.aliases.insert(String::from(key));
        self.record(at_root, keys, key, read);
    }

    fn push(&mut self, at_root: bool, keys: Vec<String>, source: &str, read: &str) {
        self.log.push(Write {
            at_root,
            keys,
            source: source.to_ascii_lowercase(),
            read: String::from(read),
        });
    }

    /// The normalized key read by the last write to exactly `key` under
    /// `properties`.
    pub fn read_at(&self, key: &str) -> Option<String> {
        self.log
            .iter()
            .rev()
            .find(|write| {
                !write.at_root
                    && write.keys.len() == 1
                    && write.keys.first().is_some_and(|k| k == key)
            })
            .map(|write| write.read.clone())
    }

    /// Whether a write of some other normalized name than `name` (dotted
    /// keys) left the value now at `keys`.
    pub fn replaced(&self, at_root: bool, keys: &[String], name: &[String]) -> bool {
        let keys: Vec<&str> = keys.iter().map(String::as_str).collect();
        self.origin(at_root, &keys)
            .is_some_and(|origin| origin.name != name.join(".").to_ascii_lowercase())
    }

    /// The write that left the value now at `keys`: the last write at or
    /// above `keys`. `None` if nothing was written there. Writes to exactly
    /// `keys` come first; keys from normalized names match the written keys
    /// in any case.
    pub fn origin(&self, at_root: bool, keys: &[&str]) -> Option<Origin> {
        let last_write = |same: fn(&str, &str) -> bool| {
            self.log.iter().rev().find(|write| {
                write.at_root == at_root
                    && write.keys.len() <= keys.len()
                    && write
                        .keys
                        .iter()
                        .zip(keys)
                        .all(|(dest, key)| same(dest, key))
            })
        };
        let write = last_write(|dest, key| dest == key)
            .or_else(|| last_write(|dest, key| dest.eq_ignore_ascii_case(key)))?;
        let below = keys.get(write.keys.len()..).unwrap_or_default();
        let name: Vec<&str> = core::iter::once(write.source.as_str())
            .chain(below.iter().copied())
            .collect();
        Some(Origin {
            name: name.join(".").to_ascii_lowercase(),
        })
    }
}

/// Re-wrap sub-resource array elements by moving non-envelope fields back
/// under each element's `properties` object.
pub fn rewrap_sub_resource_arrays(
    result: &mut ObjMap,
    properties: &mut ObjMap,
    sub_arrays: &BTreeSet<String>,
    cx: &Context<'_>,
) {
    if sub_arrays.is_empty() {
        return;
    }
    // Several short names can resolve to the same array (two plain aliases
    // with one ARM path). Wrap each array once. Keys differing only in case
    // are different arrays, so group by the keys actually in the output.
    let mut targets: BTreeMap<(bool, Vec<String>), BTreeMap<&str, ElementFields>> = BTreeMap::new();
    for sub_array_path in sub_arrays {
        let fields = cx.fields.get(sub_array_path).cloned().unwrap_or_default();
        let (at_root, keys) = written_keys(sub_array_path, cx);
        let keys: Vec<&str> = keys.iter().map(String::as_str).collect();
        let map = if at_root { &*result } else { &*properties };
        targets
            .entry((at_root, output_keys(map, &keys)))
            .or_default()
            .insert(sub_array_path.as_str(), fields);
    }

    // Deepest first, so an outer array is wrapped after the arrays inside it.
    let mut sorted: Vec<_> = targets.into_iter().collect();
    sorted.sort_by_key(|((_, keys), _)| core::cmp::Reverse(keys.len()));

    for ((at_root, keys), by_name) in sorted {
        let keys: Vec<&str> = keys.iter().map(String::as_str).collect();
        // A later write may have replaced the flattened array with a value
        // the normalizer left wrapped (another plain alias with the same ARM
        // path, or one over the array's parent). Wrap only a flattened array.
        let origin = cx.writes.origin(at_root, &keys);
        if origin
            .as_ref()
            .is_some_and(|origin| !sub_arrays.contains(&origin.name))
        {
            continue;
        }
        // Wrap by the name whose value is there. Otherwise by all the names.
        let fields = origin
            .as_ref()
            .and_then(|origin| by_name.get(origin.name.as_str()))
            .cloned()
            .unwrap_or_else(|| {
                let mut all = ElementFields::default();
                for fields in by_name.values() {
                    all.fields.extend(fields.fields.iter().cloned());
                    all.root.extend(fields.root.iter().cloned());
                }
                all
            });
        let Some((first, rest)) = keys.split_first() else {
            continue;
        };
        let map = if at_root {
            &mut *result
        } else {
            &mut *properties
        };
        if let Some(value) = obj_key_ci(map, first).and_then(|key| map.get_mut(key.as_ref())) {
            rewrap_at(value, rest, &fields, cx.casing_map);
        }
    }
}

/// The keys in `map` that `keys` lead to: each key as it is in the output
/// (exact match first, else the smallest that differs only in case, as
/// element remaps pick), as far as objects go. Keys inside arrays are matched
/// per element and kept as given.
pub fn output_keys(map: &ObjMap, keys: &[&str]) -> Vec<String> {
    let mut out = Vec::with_capacity(keys.len());
    let mut current: Option<&Value> = None;
    for (i, key) in keys.iter().enumerate() {
        let found = match current {
            None => {
                obj_key_ci(map, key).and_then(|k| Some((String::from(k.as_ref()), map.get(&k)?)))
            }
            Some(Value::Object(obj)) => find_key_ci_btree(obj, key).and_then(|k| {
                let name = String::from(val_str(&k)?);
                Some((name, obj.get(&k)?))
            }),
            Some(_) => None,
        };
        match found {
            Some((name, value)) => {
                out.push(name);
                current = Some(value);
            }
            None => {
                out.extend(
                    keys.get(i..)
                        .unwrap_or_default()
                        .iter()
                        .map(|k| String::from(*k)),
                );
                break;
            }
        }
    }
    out
}

/// Where a sub-resource array sits in the denormalized output: `true` for
/// the ARM root rather than `properties`, plus the keys leading to it. When
/// phase 2b wrote a plain alias for the first key, the array is under that
/// alias's ARM path (`x` -> `properties.items` puts `x.y` at `items.y`);
/// otherwise phase 2a wrote the key as is. Keys from the short name get the
/// casing those phases restored, so a sibling that differs only in case is
/// not taken for the array.
fn written_keys(sub_array_path: &str, cx: &Context<'_>) -> (bool, Vec<String>) {
    let names: Vec<&str> = sub_array_path.split('.').collect();
    let restore = |part: &[&str]| -> Vec<String> {
        part.iter()
            .map(|name| restore_casing(name, cx.casing_map))
            .collect()
    };
    let Some((first, rest)) = names.split_first() else {
        return (cx.is_data_plane, restore(&names));
    };
    match alias_location(first, cx.entries, cx.api_version, cx.writes) {
        Some((at_root, arm)) => {
            let mut keys: Vec<String> = arm.into_iter().map(String::from).collect();
            keys.extend(restore(rest));
            (at_root, keys)
        }
        // Phase 2a writes root fields (`sku`) at the root.
        None => {
            let root = ROOT_FIELDS.iter().any(|f| f.eq_ignore_ascii_case(first));
            (cx.is_data_plane || root, restore(&names))
        }
    }
}

/// Where phase 2b wrote the plain alias `key`: `true` for the ARM root
/// rather than `properties`, plus its ARM keys. `None` if it wrote nothing
/// for `key`.
fn alias_location<'a>(
    key: &str,
    entries: &'a BTreeMap<String, ResolvedEntry>,
    api_version: Option<&str>,
    writes: &Writes,
) -> Option<(bool, Vec<&'a str>)> {
    if !writes.aliases.contains(key) {
        return None;
    }
    let arm = entries.get(key)?.select_path(api_version);
    let (at_root, arm) = arm
        .strip_prefix("properties.")
        .map_or((true, arm), |inner| (false, inner));
    Some((at_root, arm.split('.').collect()))
}

/// Point an element remap's array chain at where phase 2b wrote its outer
/// array: `true` for the ARM root rather than `properties`, plus the chain
/// with its first key replaced by the alias's ARM keys. `None` if phase 2b
/// did not write the first key.
pub fn redirect_chain(
    chain: &[Vec<String>],
    entries: &BTreeMap<String, ResolvedEntry>,
    api_version: Option<&str>,
    writes: &Writes,
) -> Option<(bool, Vec<Vec<String>>)> {
    let (outer, inner) = chain.split_first()?;
    let (first, rest) = outer.split_first()?;
    let (at_root, arm) = alias_location(first, entries, api_version, writes)?;
    let redirected = arm
        .into_iter()
        .map(String::from)
        .chain(rest.iter().cloned())
        .collect();
    Some((
        at_root,
        core::iter::once(redirected)
            .chain(inner.iter().cloned())
            .collect(),
    ))
}

/// Follow `keys` from `value` and re-wrap the elements of the array there.
/// Like the normalizer's path tracking, arrays along the way are walked
/// element by element and objects by key, so a name such as `a.b.c` matches
/// `a.b[*].c[*]` and `a[*].b[*].c[*]` alike.
fn rewrap_at(
    value: &mut Value,
    keys: &[&str],
    fields: &ElementFields,
    casing: &BTreeMap<String, String>,
) {
    match value {
        Value::Array(arr) => {
            for elem in crate::Rc::make_mut(arr).iter_mut() {
                if keys.is_empty() {
                    *elem = rewrap_element(elem, fields, casing);
                } else {
                    rewrap_at(elem, keys, fields, casing);
                }
            }
        }
        Value::Object(obj) => {
            let Some((first, rest)) = keys.split_first() else {
                return;
            };
            let obj = crate::Rc::make_mut(obj);
            if let Some(key) = find_key_ci_btree(obj, first) {
                if let Some(child) = obj.get_mut(&key) {
                    rewrap_at(child, rest, fields, casing);
                }
            }
        }
        _ => {}
    }
}

/// Find a key in a BTreeMap: the exact key, else any case-insensitive match.
fn find_key_ci_btree(btree: &Object, key: &str) -> Option<Value> {
    let exact = Value::String(crate::Rc::from(key));
    if btree.contains_key(&exact) {
        return Some(exact);
    }
    btree
        .keys()
        .find(|k| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case(key)))
        .cloned()
}

/// Re-wrap a single sub-resource array element, the reverse of the
/// normalizer's `flatten_element`: aliased fields go back to their ARM names
/// inside or outside the `properties` wrapper, `_p_<name>` fields inside it,
/// and other fields inside it unless an alias reads them at the root or they
/// are standard envelope fields (`name`).
fn rewrap_element(
    element: &Value,
    fields: &ElementFields,
    casing: &BTreeMap<String, String>,
) -> Value {
    let Ok(obj) = element.as_object() else {
        return element.clone();
    };

    let mut rest = obj.clone();
    let mut envelope = Object::new();
    let mut props = Object::new();
    for field in &fields.fields {
        if let Some(value) = take_dotted_path_obj(&mut rest, &field.short) {
            let keys: Vec<&str> = field.arm.split('.').collect();
            let target = if field.wrapped {
                &mut props
            } else {
                &mut envelope
            };
            set_nested(target, &keys, value, false);
        }
    }

    // Escaped wrapped fields first, so they win over an unescaped namesake.
    let mut leftovers: Vec<(&Value, &Value)> = rest.iter().collect();
    leftovers.sort_by_key(|(key, _)| !val_str(key).is_some_and(|k| k.starts_with("_p_")));
    for (key, val) in leftovers {
        let Some(key_s) = val_str(key) else {
            continue;
        };
        if let Some(name) = key_s.strip_prefix("_p_") {
            merge_absent(&mut props, restore_casing(name, casing), val.clone());
        } else if is_element_envelope_field(key_s)
            || fields.root.contains(&key_s.to_ascii_lowercase())
        {
            merge_absent(&mut envelope, String::from(key_s), val.clone());
        } else {
            merge_absent(&mut props, String::from(key_s), val.clone());
        }
    }

    if !props.is_empty() {
        envelope.insert(Value::from("properties"), Value::from(props));
    }
    Value::from(envelope)
}

/// Insert `value` at `key` unless the key is there, merging objects.
fn merge_absent(obj: &mut Object, key: String, value: Value) {
    let key = Value::from(key);
    let Some(existing) = obj.get_mut(&key) else {
        obj.insert(key, value);
        return;
    };
    if let (Value::Object(existing), Value::Object(value)) = (existing, &value) {
        let existing = crate::Rc::make_mut(existing);
        for (k, v) in value.iter() {
            if let Some(k) = val_str(k) {
                merge_absent(existing, String::from(k), v.clone());
            }
        }
    }
}
