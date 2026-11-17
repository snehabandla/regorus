// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Per-alias path resolution: reads values from versioned ARM paths and places
//! them at alias short name paths in the normalized output.

use crate::Rc;
use crate::Value;

use super::super::obj_map::{
    collision_safe_key, is_root_field_collision, obj_insert_rc, set_nested_lowercased, ObjMap,
};
use super::super::path;
use super::super::types::ResolvedAliases;
use super::element_remap::apply_element_remap_precomputed;
use super::flatten::normalize_value;

/// Apply per-alias path resolution to the normalized result.
///
/// Uses precomputed element remaps and array renames from [`ResolvedAliases`]
/// when `api_version` is `None` (the common case). Falls back to dynamic
/// computation when a specific `api_version` is provided.
pub fn apply_alias_entries(
    result: &mut ObjMap,
    raw: &Value,
    aliases: &ResolvedAliases,
    api_version: Option<&str>,
) {
    let entries = &aliases.entries;
    let sub_resource_set = &aliases.sub_resource_arrays;

    for (lc_key, entry) in entries {
        if entry.is_wildcard || !entry.has_valid_short_name() {
            continue;
        }

        // Skip sub-resource array root entries.
        if sub_resource_set.contains(lc_key.as_str()) {
            continue;
        }

        // Use the precomputed parsed path (default or versioned).
        let Some(value) = entry
            .select_arm_path(api_version)
            .and_then(|arm| path::get(raw, &arm.segments, false))
        else {
            continue;
        };
        let value = normalize_value(value, &entry.short_name, None);

        if is_root_field_collision(&entry.short_name, &entry.default_path) {
            let target = collision_safe_key(&entry.short_name);
            set_nested_lowercased(result, &target, value);
        } else if entry.short_name.contains(['.', '[']) {
            set_nested_lowercased(result, &entry.short_name, value);
        } else {
            obj_insert_rc(result, Rc::clone(&entry.short_name_lc), value);
        }
    }

    // Look up precomputed aggregates: default or per-version.
    let agg = api_version.map_or(&aliases.default_aggregates, |ver| {
        let ver_lc = ver.to_ascii_lowercase();
        aliases
            .versioned_aggregates
            .get(&ver_lc)
            .unwrap_or(&aliases.default_aggregates)
    });

    for remap in &agg.element_remaps {
        // Moves the ARM field so the normalized output only has the alias
        // short name; a stale source would duplicate under restored casing.
        apply_element_remap_precomputed(result, remap);
    }

    for (source_lc, target_lc) in &agg.array_renames_normalize {
        path::rename(result, source_lc, target_lc, true);
    }
}
