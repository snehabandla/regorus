// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Normalized `input.resource` → ARM JSON reverse transformation.

mod casing;
pub(crate) mod helpers;
mod sub_resource;

#[cfg(test)]
mod tests;

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use crate::Value;

use crate::Rc;

use super::obj_map::{
    extract_type_field, is_root_field_collision, make_value, new_map, obj_insert, val_str,
    ROOT_FIELDS,
};
use super::path::{self, Segment};
use super::types::ResolvedAliases;
use super::AliasRegistry;

use super::normalizer::{apply_element_remap, ElementRemap};

use casing::{build_casing_map, default_casing_map, denormalize_value, restore_casing};
use helpers::find_key_ci;

/// Denormalize a normalized resource back to ARM JSON structure.
pub fn denormalize(
    normalized: &Value,
    registry: Option<&AliasRegistry>,
    api_version: Option<&str>,
) -> Value {
    let aliases = registry.and_then(|r| extract_type_field(normalized).and_then(|rt| r.get(rt)));
    denormalize_with_aliases(normalized, aliases, api_version)
}

/// Internal denormalization with pre-resolved alias data.
pub fn denormalize_with_aliases(
    normalized: &Value,
    aliases: Option<&ResolvedAliases>,
    api_version: Option<&str>,
) -> Value {
    let obj = match normalized.as_object() {
        Ok(o) => o,
        Err(_) => return normalized.clone(),
    };

    let entries = aliases.map(|a| &a.entries);
    let casing_map = entries
        .map(build_casing_map)
        .unwrap_or_else(default_casing_map);
    let empty_set = BTreeSet::new();
    let sub_resource_set = aliases.map_or(&empty_set, |a| &a.sub_resource_arrays);

    let is_data_plane =
        extract_type_field(normalized).is_some_and(|t| t.to_ascii_lowercase().contains(".data/"));

    let mut result = new_map();
    let mut properties = new_map();

    // Phase 1: Root fields → ARM root with original casing.
    for &field in ROOT_FIELDS {
        let lc = field.to_ascii_lowercase();
        // Fast-path: direct BTreeMap lookup (O(log N)) for the common case
        // where normalized input was produced by our normalizer with lowercase keys.
        // Falls back to linear case-insensitive scan for externally-supplied mixed-case input.
        let lc_key = Value::String(Rc::from(lc.as_str()));
        let found = obj.get(&lc_key).or_else(|| {
            obj.iter()
                .find(|(k, _)| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case(&lc)))
                .map(|(_, v)| v)
        });
        if let Some(val) = found {
            let restored = denormalize_value(val, &casing_map);
            obj_insert(&mut result, field, restored);
        }
    }

    // What phases 2a, 2b and 2c write, in order; later phases look for plain
    // aliases at their ARM paths, and wrap only arrays still flattened.
    let mut writes = sub_resource::Writes::default();

    // Phase 2a: Non-aliased, non-root fields.
    for (key, val) in obj.iter() {
        let key_s = match val_str(key) {
            Some(s) => s,
            None => continue,
        };
        if ROOT_FIELDS.iter().any(|f| f.eq_ignore_ascii_case(key_s)) {
            continue;
        }

        let lookup_key = key_s.strip_prefix("_p_").unwrap_or(key_s);
        let lookup_key_lc = lookup_key.to_ascii_lowercase();
        let has_alias = entries.is_some_and(|e| e.contains_key(lookup_key_lc.as_str()));
        if has_alias {
            continue;
        }

        let denorm_val = denormalize_value(val, &casing_map);

        if key_s.starts_with("_p_") {
            let restored = restore_casing(lookup_key, &casing_map);
            writes.record_key(false, &restored, lookup_key, key_s);
            obj_insert(&mut properties, &restored, denorm_val);
        } else if is_data_plane {
            let restored = restore_casing(key_s, &casing_map);
            writes.record_key(true, &restored, key_s, key_s);
            obj_insert(&mut result, &restored, denorm_val);
        } else {
            let restored = restore_casing(key_s, &casing_map);
            writes.record_key(false, &restored, key_s, key_s);
            obj_insert(&mut properties, &restored, denorm_val);
        }
    }

    // Phase 2b: Aliased scalar fields → versioned ARM paths. A plain dotted
    // short name of several keys is read at its nested path and moved out of
    // where phase 1 or 2a put it; other short names are one key, which phase
    // 2a skipped. Short names that are not plain dotted keys (`x. legacy`)
    // are looked up as one key, though the normalizer wrote them nested.
    // Sources are removed before any value is written, so a write is not
    // consumed as another alias's source. A moved value whose write fails
    // stays at its source; a refused single-key write leaves no value.
    if let Some(entries) = entries {
        let mut moves = Vec::new();
        for (lc_key, entry) in entries {
            if entry.is_wildcard {
                continue;
            }

            if sub_resource_set.contains(lc_key.as_str()) {
                continue;
            }

            let normalized_key = if is_root_field_collision(&entry.short_name, &entry.default_path)
            {
                alloc::format!("_p_{}", entry.short_name.to_ascii_lowercase())
            } else {
                lc_key.clone()
            };

            // Fast-path: direct BTreeMap lookup for lowercase keys,
            // with case-insensitive fallback for mixed-case external input.
            let nk_val = Value::String(Rc::from(normalized_key.as_str()));
            let found = obj.get(&nk_val).map(|v| (&nk_val, v)).or_else(|| {
                obj.iter().find(|(k, _)| {
                    val_str(k).is_some_and(|s| s.eq_ignore_ascii_case(&normalized_key))
                })
            });
            let arm = entry.select_path_segments(api_version);
            let (at_root, target) = match arm.split_first() {
                Some((Segment::Key(key), rest)) if &**key == "properties" && !rest.is_empty() => {
                    (false, rest)
                }
                _ => (true, arm),
            };
            let short = entry.short_segments.as_slice();
            let (read, val, source) = match short {
                [Segment::Key(first), _, ..] if entry.nested_short_name => {
                    // Not moved: a key phase 2a skipped as another alias's or
                    // renamed from a collision key, a root field phase 1
                    // copied whole, and a non-dotted ARM path.
                    let first = first.to_ascii_lowercase();
                    if entries.contains_key(first.as_str())
                        || first.starts_with("_p_")
                        || ROOT_FIELDS.iter().any(|f| f.eq_ignore_ascii_case(&first))
                        || !path::renders_dotted(arm)
                        || arm
                            .iter()
                            .any(|s| matches!(s, Segment::Key(k) if k.is_empty()))
                    {
                        continue;
                    }
                    let Some(val) = path::get(normalized, short, true) else {
                        continue;
                    };
                    if is_data_plane == at_root && path::equivalent(short, target) {
                        continue;
                    }
                    (lc_key.clone(), val, Some(is_data_plane))
                }
                _ => {
                    let Some((read, val)) = found.and_then(|(k, v)| Some((val_str(k)?, v))) else {
                        continue;
                    };
                    (String::from(read), val, None)
                }
            };
            let value = denormalize_value(val, &casing_map);
            moves.push(ScalarWrite {
                key: lc_key,
                read,
                short,
                source,
                at_root,
                target,
                value,
                written: true,
            });
        }

        // A shorter target written later would replace a longer one.
        moves.sort_by_key(|write| write.target.len());
        let backup = moves
            .iter()
            .any(|write| write.source.is_some())
            .then(|| (properties.clone(), result.clone()));
        loop {
            for write in moves.iter().filter(|write| write.written) {
                match write.source {
                    Some(true) => path::remove(&mut result, write.short),
                    Some(false) => path::remove(&mut properties, write.short),
                    None => {}
                }
            }
            let mut retry = false;
            for write in moves.iter_mut().filter(|write| write.written) {
                let map = if write.at_root {
                    &mut result
                } else {
                    &mut properties
                };
                // Phase 4 replaces a non-object `properties`.
                let replaced = write.source.is_some()
                    && write.at_root
                    && matches!(write.target, [Segment::Key(key)] if &**key == "properties")
                    && !matches!(write.value, Value::Object(_));
                if replaced || !path::set_keys(map, write.target, write.value.clone(), false) {
                    write.written = false;
                    retry |= write.source.is_some();
                }
            }
            match (&backup, retry) {
                (Some((p, r)), true) => (properties, result) = (p.clone(), r.clone()),
                _ => break,
            }
        }
        for write in moves.iter().filter(|write| write.written) {
            writes.record_alias(write.at_root, write.target, write.key, &write.read);
        }

        // Phase 2c + 2d: Use precomputed renames/remaps.
        // Look up versioned aggregates when api_version is provided,
        // falling back to default aggregates.
        if let Some(aliases) = aliases {
            let agg = api_version.map_or(&aliases.default_aggregates, |ver| {
                let ver_lc = ver.to_ascii_lowercase();
                aliases
                    .versioned_aggregates
                    .get(&ver_lc)
                    .unwrap_or(&aliases.default_aggregates)
            });

            // Phase 2c: Precomputed array base renames.
            // Each rename as (alias base, ARM base), in order.
            let mut renamed: Vec<(&str, &str)> = Vec::new();
            for (alias_base_lc, arm_base) in &agg.array_renames_denormalize {
                if let Some(key) = find_key_ci(&properties, alias_base_lc) {
                    if let Some(val) = properties.remove(key.as_ref()) {
                        obj_insert(&mut properties, arm_base, val);
                        renamed.push((alias_base_lc, arm_base));
                        // The normalizer flattened and remapped this value under its ARM name.
                        let read = writes
                            .read_at(&key)
                            .unwrap_or_else(|| alloc::string::String::from(&*key));
                        writes.record_key(false, arm_base, arm_base, &read);
                    }
                }
            }

            // Phase 2d: Precomputed reverse element-level field remaps.
            for rev in &agg.reverse_element_remaps {
                let remap = ElementRemap {
                    array_chain: rev.array_chain.clone(),
                    source_field: path::alias_segments(&rev.source_field),
                    target_field: path::alias_segments(&rev.target_field)
                        .into_iter()
                        .map(|segment| match segment {
                            Segment::Key(key) => {
                                Segment::Key(Rc::from(restore_casing(&key, &casing_map)))
                            }
                            other => other,
                        })
                        .collect(),
                };
                // Follow an outer array phase 2b moved to its ARM path, or
                // phase 2c renamed (the normalizer remapped it after renaming).
                // Otherwise phase 2a wrote it: at the root of a data-plane
                // resource when the alias's arrays are there under the same
                // names, else in `properties`.
                // Phase 2c records a rename under the ARM base's name.
                let alias_name = remap.array_chain.first().cloned();
                let (at_root, array_chain, name) =
                    sub_resource::redirect_chain(&remap.array_chain, entries, api_version, &writes)
                        .map(|(at_root, chain)| (at_root, chain, alias_name.clone()))
                        .or_else(|| {
                            renamed_chain(&remap.array_chain, &renamed).map(|(arm_base, chain)| {
                                (false, chain, Some(alloc::vec![String::from(arm_base)]))
                            })
                        })
                        .unwrap_or_else(|| {
                            (
                                is_data_plane && rev.at_root,
                                remap.array_chain.clone(),
                                alias_name,
                            )
                        });
                // Another alias's value replaced this one there; it was not
                // remapped with this alias's names.
                // Check the keys the remap will reach, so an older write to an
                // exact ancestor does not hide a later write that differs in case.
                if let (Some(outer), Some(name)) = (array_chain.first(), name.as_ref()) {
                    let map = if at_root { &result } else { &properties };
                    let outer: alloc::vec::Vec<&str> =
                        outer.iter().map(|key| key.as_str()).collect();
                    let reached = sub_resource::output_keys(map, &outer);
                    if writes.replaced(at_root, &reached, name) {
                        continue;
                    }
                }
                let map = if at_root {
                    &mut result
                } else {
                    &mut properties
                };
                let remap = ElementRemap {
                    array_chain,
                    ..remap
                };
                apply_element_remap(map, &remap, false);
            }
        }
    }

    // Phase 3: Re-wrap sub-resource array elements.
    if let Some(aliases) = aliases {
        if !aliases.sub_resource_arrays.is_empty() {
            let cx = sub_resource::Context {
                entries: &aliases.entries,
                api_version,
                writes: &writes,
                is_data_plane,
                casing_map: &casing_map,
                normalized: obj,
            };
            sub_resource::rewrap_sub_resource_arrays(
                &mut result,
                &mut properties,
                &aliases.sub_resource_arrays,
                &cx,
            );
        }
    }

    // Phase 4: Attach properties to result.
    if !properties.is_empty() {
        if let Some(Value::Object(existing_rc)) = result.get_mut("properties") {
            // Merge directly into the Object, avoiding full ObjMap round-trip.
            let existing = Rc::make_mut(existing_rc);
            for (k, v) in properties {
                existing.get_or_insert_with(Value::String(k), || v);
            }
        } else {
            obj_insert(&mut result, "properties", make_value(properties));
        }
    }

    make_value(result)
}

/// A phase 2b write of a plain alias's value at its ARM path.
struct ScalarWrite<'a> {
    /// The alias's lowercase short name.
    key: &'a str,
    /// The normalized key the value was read from.
    read: String,
    short: &'a [Segment],
    /// Where phase 1 or 2a put a value that is moved: `Some(true)` at the
    /// ARM root, `Some(false)` in `properties`.
    source: Option<bool>,
    at_root: bool,
    target: &'a [Segment],
    value: Value,
    written: bool,
}

/// Point an element remap's array chain at the ARM base phase 2c renamed its
/// outer array to: the ARM base, plus the chain with its first key replaced.
/// `None` if phase 2c did not rename it, or a later rename replaced or moved
/// it. A dotted base is a literal key to the rename but nested keys to the
/// normalizer's remaps, which therefore never applied; it is `None` too.
fn renamed_chain<'a>(
    chain: &[Vec<String>],
    renamed: &[(&str, &'a str)],
) -> Option<(&'a str, Vec<Vec<String>>)> {
    let (outer, inner) = chain.split_first()?;
    let [alias_base] = outer.as_slice() else {
        return None;
    };
    let at = renamed
        .iter()
        .rposition(|(alias, _)| alias.eq_ignore_ascii_case(alias_base))?;
    let &(_, arm_base) = renamed.get(at)?;
    let later = renamed.get(at.saturating_add(1)..).unwrap_or_default();
    if later.iter().any(|(alias, arm)| {
        arm.eq_ignore_ascii_case(arm_base) || alias.eq_ignore_ascii_case(arm_base)
    }) {
        return None;
    }
    let redirected = alloc::vec![String::from(arm_base)];
    Some((
        arm_base,
        core::iter::once(redirected)
            .chain(inner.iter().cloned())
            .collect(),
    ))
}
