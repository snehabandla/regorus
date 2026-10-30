// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects,
    clippy::unwrap_used,
    clippy::shadow_unrelated,
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

use super::{
    CompilationContext, Compiler, CompilerError, ContextType, HeadKey, ObjectHead, Register,
    Result, SpannedCompilerError, WorklistEntry,
};
use crate::ast::{Expr, ExprRef, NodeRef, Rule, RuleHead};
use crate::compiler::destructuring_planner::plans::BindingPlan;
use crate::lexer::Span;
use crate::parser::Parser;
use crate::rvm::instructions::{ChainedIndexParams, LiteralOrRegister};
use crate::rvm::program::{Program, RuleType, SpanInfo};
use crate::rvm::Instruction;
use crate::utils::{format_string_path, get_path_string, get_rule_path_components};
use crate::Map;
use crate::{CompiledPolicy, Value};
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::{String, ToString};
use alloc::sync::Arc;
use alloc::vec::Vec;

/// One element of a rule head reference.
enum HeadItem {
    Root,
    Field(Value),
    Index(ExprRef),
}

/// How a rule definition contributes to the document at a rule path.
#[derive(Clone)]
struct DefinitionShape {
    rule_type: RuleType,
    /// Keys below the rule path; non-empty exactly for partial objects.
    keys: Vec<HeadKey>,
    /// `contains` heads: the contributed value is a set element.
    multi_value: bool,
    /// Element of a Rego v0 `p.x { ... }` set rule.
    value_literal: Option<Value>,
}

impl DefinitionShape {
    const fn complete() -> Self {
        Self {
            rule_type: RuleType::Complete,
            keys: Vec::new(),
            multi_value: false,
            value_literal: None,
        }
    }
}

impl<'a> Compiler<'a> {
    /// Extract a compile-time constant `Value` from an optional expression.
    /// Returns `Some(Value::Bool(true))` for the implicit-true case (`expr_ref`
    /// is `None`), delegates to `try_eval_const` for actual expressions.
    fn static_value_of_expr(expr_ref: &Option<ExprRef>) -> Option<Value> {
        match expr_ref {
            None => Some(Value::Bool(true)),
            Some(expr) => super::expressions::try_eval_const(expr.as_ref()),
        }
    }

    pub(super) fn compute_rule_type(&self, rule_path: &str) -> Result<RuleType> {
        // A default registered here for a longer path (`default p.r := 0`
        // at `p`) makes the document at `rule_path` an object.
        let mut nested_default = false;
        for (default_rule, _) in self
            .policy
            .inner
            .default_rules
            .get(rule_path)
            .into_iter()
            .flatten()
        {
            if let Rule::Default { refr, .. } = default_rule.as_ref() {
                let mut items = Vec::new();
                Self::collect_head_items(refr, &mut items)?;
                nested_default |= items.len() > self.head_items_on_path(rule_path, default_rule)?;
            }
        }

        let Some(definitions) = self.policy.inner.rules.get(rule_path) else {
            // Default-only rules (e.g., `default deny := true`) have no regular definitions
            // in the `rules` map — they only exist in `default_rules`. Treat them as Complete.
            if self.policy.inner.default_rules.contains_key(rule_path) {
                return Ok(RuleType::Complete);
            }
            return Err(CompilerError::General {
                message: format!("no definitions found for rule path '{}'", rule_path),
            }
            .into());
        };

        let mut rule_types = BTreeSet::new();
        let mut leaf_kinds = BTreeMap::new();
        let shapes = self.definition_shapes(rule_path, definitions)?;
        for shape in &shapes {
            // Definitions rooted at the same static prefix cannot mix
            // single-value and set-valued heads, even if their dynamic keys
            // happen to be disjoint for this input.
            if leaf_kinds
                .insert(Self::static_head_prefix(shape), shape.multi_value)
                .is_some_and(|multi_value| multi_value != shape.multi_value)
            {
                return Err(CompilerError::ConflictingRuleTypes {
                    rule_path: rule_path.to_string(),
                }
                .into());
            }
            let prefix = Self::static_head_prefix(shape);
            if prefix.len() == shape.keys.len()
                && shapes.iter().any(|other| {
                    other.keys.len() > prefix.len()
                        && Self::static_head_prefix(other).starts_with(&prefix)
                })
            {
                return Err(CompilerError::ConflictingRuleTypes {
                    rule_path: rule_path.to_string(),
                }
                .into());
            }
            rule_types.insert(shape.rule_type.clone());
        }

        if nested_default {
            rule_types.insert(RuleType::PartialObject);
        }
        if rule_types.len() > 1 {
            return Err(CompilerError::ConflictingRuleTypes {
                rule_path: rule_path.to_string(),
            }
            .into());
        }

        rule_types.into_iter().next().ok_or_else(|| {
            CompilerError::RuleTypeNotFound {
                rule_path: rule_path.to_string(),
            }
            .into()
        })
    }

    fn static_head_prefix(shape: &DefinitionShape) -> Vec<Value> {
        shape
            .keys
            .iter()
            .map_while(|key| match key {
                HeadKey::Field(value) => Some(value.clone()),
                HeadKey::Expr(expr) => super::expressions::try_eval_const(expr),
            })
            .take_while(|key| *key != Value::Undefined)
            .collect()
    }

    pub(super) fn retain_owned_partial_object_defaults(
        &self,
        rule_path: &str,
        defaults: &mut Value,
    ) -> Result<()> {
        let Some(definitions) = self.policy.inner.rules.get(rule_path) else {
            return Ok(());
        };
        for shape in self.definition_shapes(rule_path, definitions)? {
            let prefix = Self::static_head_prefix(&shape);
            if prefix.len() == shape.keys.len() {
                continue;
            }
            // A dynamically keyed document does not inherit defaults from
            // separately registered static children.
            let Some((last, ancestors)) = prefix.split_last() else {
                *defaults = Value::Undefined;
                return Ok(());
            };
            let current = ancestors.iter().try_fold(&mut *defaults, |value, key| {
                value.as_object_mut().ok()?.get_mut(key)
            });
            if let Some(current) = current {
                if let Ok(object) = current.as_object_mut() {
                    object.remove(last);
                }
            }
        }
        Ok(())
    }

    pub(super) fn encode_partial_object_defaults(
        &self,
        rule_path: &str,
        defaults: &Value,
    ) -> Result<Value> {
        let mut entries = Vec::new();
        for (rule, _) in self
            .policy
            .inner
            .default_rules
            .get(rule_path)
            .into_iter()
            .flatten()
        {
            let Rule::Default { refr, .. } = rule.as_ref() else {
                continue;
            };
            let mut items = Vec::new();
            Self::collect_head_items(refr, &mut items)?;
            let consumed = self.head_items_on_path(rule_path, rule)?;
            let mut path = Vec::new();
            for item in items.into_iter().skip(consumed) {
                let key =
                    match item {
                        HeadItem::Field(value) => value,
                        HeadItem::Index(expr) => super::expressions::try_eval_const(&expr)
                            .ok_or_else(|| CompilerError::UnsupportedRuleHeadPath {
                                rule_path: rule_path.to_string(),
                            })?,
                        HeadItem::Root => continue,
                    };
                path.push(key);
            }
            if path.is_empty() {
                continue;
            }
            let value = path
                .iter()
                .try_fold(defaults, |value, key| value.as_object().ok()?.get(key));
            if let Some(value) = value.filter(|value| **value != Value::Undefined) {
                entries.push(Value::from_array(alloc::vec![
                    Value::from_array(path),
                    value.clone(),
                ]));
            }
        }
        Ok(Value::from_array(entries))
    }

    /// Static partial documents exist even when none of their bodies match:
    /// `p.q[k] contains v` contributes `q: {}`, and `p.a contains v`
    /// contributes `a: set()`. Dynamic head keys do not materialize ancestors
    /// beyond their first unknown key.
    fn initial_partial_object(rule_path: &str, shapes: &[DefinitionShape]) -> Result<Value> {
        let mut initial = Value::new_object();
        let prefixes: Vec<Vec<Value>> = shapes.iter().map(Self::static_head_prefix).collect();
        for (shape, prefix) in shapes.iter().zip(&prefixes) {
            let mut keys = prefix.clone();
            let mut leaf = if keys.len() == shape.keys.len() && shape.multi_value {
                Value::new_set()
            } else {
                if keys.len() == shape.keys.len() {
                    keys.pop();
                }
                Value::new_object()
            };
            // A dynamic ancestor owns the document's empty result. Both
            // static set leaves and virtual-object prefixes beneath it only
            // appear when their definitions contribute a value.
            for (other, prefix) in shapes.iter().zip(&prefixes) {
                if prefix.len() < other.keys.len()
                    && keys.len() > prefix.len()
                    && keys.starts_with(prefix)
                {
                    keys.truncate(prefix.len());
                    leaf = Value::new_object();
                }
            }
            let Some((last, ancestors)) = keys.split_last() else {
                continue;
            };
            let conflict = || CompilerError::ConflictingRuleTypes {
                rule_path: rule_path.to_string(),
            };
            let mut current = &mut initial;
            for key in ancestors {
                let object = current.as_object_mut().map_err(|_| conflict())?;
                current = object.get_or_insert_with(key.clone(), Value::new_object);
            }
            let object = current.as_object_mut().map_err(|_| conflict())?;
            match object.get(last) {
                Some(existing)
                    if matches!((existing, &leaf), (Value::Object(_), Value::Object(_)))
                        || *existing == leaf => {}
                Some(_) => return Err(conflict().into()),
                None => {
                    object.insert(last.clone(), leaf);
                }
            }
        }
        Ok(initial)
    }

    /// Shapes of the definitions registered at `rule_path` that contribute
    /// to its document. Functions and definitions that reach `rule_path` only
    /// through a variable head key (see `is_variable_key_rule_path`) belong to
    /// a shorter path and are skipped.
    fn definition_shapes(
        &self,
        rule_path: &str,
        definitions: &[NodeRef<Rule>],
    ) -> Result<Vec<DefinitionShape>> {
        let mut shapes = Vec::with_capacity(definitions.len());
        for definition in definitions {
            if let Some(shape) = self.definition_shape(rule_path, definition)? {
                shapes.push(shape);
            }
        }
        Ok(shapes)
    }

    /// True if every definition at `rule_path` reaches it through a variable
    /// head key. The interpreter registers `p[k][j] := v` under `p.k` (named
    /// after the variable), but no document lives there: the definition
    /// belongs to `p`, so such paths are not separate rules for the RVM.
    pub(super) fn is_variable_key_rule_path(&self, rule_path: &str) -> Result<bool> {
        if self.policy.inner.default_rules.contains_key(rule_path) {
            return Ok(false);
        }
        let Some(definitions) = self.policy.inner.rules.get(rule_path) else {
            return Ok(false);
        };
        for definition in definitions {
            if self.definition_shape(rule_path, definition)?.is_some() {
                return Ok(false);
            }
        }
        Ok(!definitions.is_empty())
    }

    /// True if `rule_path` can be compiled as a rule of its own: it is
    /// registered, is not a variable-key path, and every definition that can
    /// contribute to its document is registered at it. A definition at a
    /// shorter path whose head key there is a variable (`p[k] contains v`
    /// against `p.a`) may also write under `rule_path`; such a path must be
    /// read through the shorter rule instead.
    pub(super) fn is_rule_path_for_lookup(&self, rule_path: &str) -> Result<bool> {
        let inner = &self.policy.inner;
        if !inner.rules.contains_key(rule_path) && !inner.default_rules.contains_key(rule_path) {
            return Ok(false);
        }
        if self.is_variable_key_rule_path(rule_path)? {
            return Ok(false);
        }
        let Some(components) = inner.rule_path_components.get(rule_path) else {
            return Ok(false);
        };
        let registered = inner.rules.get(rule_path);
        for prefix_len in 2..components.len() {
            let prefix: Vec<&str> = components[..prefix_len]
                .iter()
                .map(String::as_str)
                .collect();
            let prefix_path = format_string_path(&prefix).map_err(CompilerError::from)?;
            let Some(definitions) = inner.rules.get(&prefix_path) else {
                continue;
            };
            // Surface conflicts between the definitions of the enclosing
            // document even when only part of it is read.
            if !self.is_variable_key_rule_path(&prefix_path)? {
                self.compute_rule_type(&prefix_path)?;
            }
            let below = &components[prefix_len..];
            for definition in definitions {
                if registered.is_some_and(|rules| rules.iter().any(|rule| rule == definition))
                    && self.definition_shape(rule_path, definition)?.is_some()
                {
                    continue;
                }
                let Some(shape) = self.definition_shape(&prefix_path, definition)? else {
                    continue;
                };
                let may_contribute = !shape.keys.is_empty()
                    && shape
                        .keys
                        .iter()
                        .zip(below)
                        .all(|(key, component)| match key {
                            HeadKey::Field(field) => field
                                .as_string()
                                .is_ok_and(|field| field.as_ref() == component),
                            HeadKey::Expr(_) => true,
                        });
                if may_contribute {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    /// Determine how a rule definition contributes to the document at
    /// `rule_path`. A definition is registered at every prefix of its head
    /// reference, so the head keys below `rule_path` decide its shape:
    /// `p.q[k] contains v` is a partial object `{q: {k: {v}}}` at `p`, a
    /// partial object `{k: {v}}` at `p.q`; `p.r := 1` is a partial object
    /// at `p` and a complete rule at `p.r`. Returns `None` if `rule_path` is
    /// reached through a variable head key.
    fn definition_shape(
        &self,
        rule_path: &str,
        rule: &NodeRef<Rule>,
    ) -> Result<Option<DefinitionShape>> {
        let Rule::Spec { head, .. } = rule.as_ref() else {
            return Ok(Some(DefinitionShape::complete()));
        };
        let (refr, is_set, is_func, set_key_missing) = match head {
            RuleHead::Compr { refr, .. } => (refr, false, false, false),
            RuleHead::Set { refr, key, .. } => (refr, true, false, key.is_none()),
            RuleHead::Func { refr, .. } => (refr, false, true, false),
        };

        let unsupported = || -> SpannedCompilerError {
            CompilerError::UnsupportedRuleHeadPath {
                rule_path: rule_path.to_string(),
            }
            .at(refr.span())
        };

        let mut items = Vec::new();
        Self::collect_head_items(refr, &mut items).map_err(|_| unsupported())?;

        // Rego v0 `p.x { ... }` adds the string "x" to the set `p`.
        let mut value_literal = None;
        if set_key_missing && items.len() > 1 {
            if let Some(HeadItem::Field(field)) = items.pop() {
                value_literal = Some(field);
            }
        }

        // The interpreter also registers the path components of a
        // non-string index (`p[input.role].x` at `p.input.role.x`), so a path
        // longer than the head can only be reached through such an index or
        // through the value of a Rego v0 set rule.
        let consumed = self.head_items_on_path(rule_path, rule)?;
        if consumed > items.len() {
            return Ok(None);
        }
        let consumed = Some(consumed)
            .filter(|consumed| *consumed >= 1 && *consumed <= items.len())
            .ok_or_else(unsupported)?;
        let (path_items, key_items) = items.split_at(consumed);
        // Every key on the rule path must be a static string: a variable key
        // there would make the rule path itself data dependent.
        if path_items.iter().skip(1).any(|item| {
            !matches!(item, HeadItem::Field(_))
                && !matches!(item, HeadItem::Index(index) if matches!(index.as_ref(), Expr::String { .. }))
        }) {
            return Ok(None);
        }

        let keys: Vec<HeadKey> = key_items
            .iter()
            .map(|item| match item {
                HeadItem::Field(field) => HeadKey::Field(field.clone()),
                HeadItem::Index(index) => HeadKey::Expr(index.clone()),
                HeadItem::Root => HeadKey::Field(Value::Undefined),
            })
            .collect();

        let rule_type = match (keys.is_empty(), is_set, is_func) {
            (true, true, _) => RuleType::PartialSet,
            (true, false, _) => RuleType::Complete,
            (false, _, true) => return Ok(None),
            (false, _, false) => RuleType::PartialObject,
        };

        Ok(Some(DefinitionShape {
            rule_type,
            keys,
            multi_value: is_set,
            value_literal,
        }))
    }

    /// Number of head items of `rule` (its root variable and the keys after
    /// it) that spell out `rule_path` below the package.
    fn head_items_on_path(&self, rule_path: &str, rule: &NodeRef<Rule>) -> Result<usize> {
        let rule_components = self
            .policy
            .inner
            .rule_path_components
            .get(rule_path)
            .ok_or_else(|| CompilerError::General {
                message: format!("missing components for registered rule path '{rule_path}'"),
            })?;
        let module_index = self.find_module_index_for_rule(rule)? as usize;
        let package_components = self
            .policy
            .get_modules()
            .get(module_index)
            .map(|module| get_rule_path_components(&module.package.refr))
            .transpose()
            .map_err(|e| CompilerError::General {
                message: format!("invalid package path: {e}"),
            })?
            .map_or(0, |components| components.len());
        // `data` and the package come first.
        rule_components
            .len()
            .checked_sub(package_components + 1)
            .ok_or_else(|| {
                CompilerError::General {
                    message: format!("rule path '{rule_path}' is shorter than its package"),
                }
                .into()
            })
    }

    fn collect_head_items(refr: &ExprRef, items: &mut Vec<HeadItem>) -> Result<()> {
        match refr.as_ref() {
            Expr::Var { .. } => items.push(HeadItem::Root),
            Expr::RefDot { refr, field, .. } => {
                Self::collect_head_items(refr, items)?;
                items.push(HeadItem::Field(field.1.clone()));
            }
            Expr::RefBrack { refr, index, .. } => {
                Self::collect_head_items(refr, items)?;
                items.push(HeadItem::Index(index.clone()));
            }
            _ => return Err(CompilerError::NotSimpleReferenceChain.at(refr.span())),
        }
        Ok(())
    }

    /// Emit the evaluation of entry point `rule_path` into `dest`. A rule path
    /// that other definitions may also write to (see
    /// `is_rule_path_for_lookup`) is read through the longest prefix that can
    /// be compiled on its own.
    fn emit_entry_point_lookup(&mut self, dest: Register, rule_path: &str) -> Result<()> {
        let components = self
            .policy
            .inner
            .rule_path_components
            .get(rule_path)
            .cloned();
        let Some(components) = components.filter(|_| {
            self.is_rule_path_for_lookup(rule_path)
                .map(|is_rule| !is_rule)
                .unwrap_or(false)
        }) else {
            let rule_idx = self.get_or_assign_rule_index(rule_path)?;
            self.emit_call_rule(dest, rule_idx);
            return Ok(());
        };

        for prefix_len in (2..components.len()).rev() {
            let prefix: Vec<&str> = components[..prefix_len]
                .iter()
                .map(String::as_str)
                .collect();
            let prefix_path = format_string_path(&prefix).map_err(CompilerError::from)?;
            if !self.is_rule_path_for_lookup(&prefix_path)? {
                continue;
            }
            let rule_idx = self.get_or_assign_rule_index(&prefix_path)?;
            let rule_reg = self.alloc_register()?;
            self.emit_call_rule(rule_reg, rule_idx);
            let path_components = components[prefix_len..]
                .iter()
                .map(|component| {
                    LiteralOrRegister::Literal(
                        self.add_literal(Value::String(component.as_str().into())),
                    )
                })
                .collect();
            let params_index = u16::try_from(
                self.program.instruction_data.chained_index_params.len(),
            )
            .map_err(|_| CompilerError::General {
                message: "chained index parameter table exceeds the RVM index limit".to_string(),
            })?;
            self.program
                .instruction_data
                .chained_index_params
                .push(ChainedIndexParams {
                    dest,
                    root: rule_reg,
                    path_components,
                });
            self.program
                .instructions
                .push(Instruction::ChainedIndex { params_index });
            self.spans.push(SpanInfo::new(0, 0, 0, 0));
            return Ok(());
        }

        Err(CompilerError::UnsupportedRuleHeadPath {
            rule_path: rule_path.to_string(),
        }
        .into())
    }

    pub(super) fn get_or_assign_rule_index(&mut self, rule_path: &str) -> Result<u16> {
        if let Some(&index) = self.rule_index_map.get(rule_path) {
            return Ok(index);
        }

        let rule_type = self.compute_rule_type(rule_path)?;
        let index = self.rule_index_map.len() as u16;

        self.rule_index_map.insert(rule_path.to_string(), index);
        let entry = WorklistEntry::new(rule_path.to_string(), self.current_call_stack.clone());
        self.rule_worklist.push(entry);

        while self.rule_definitions.len() <= index as usize {
            self.rule_definitions.push(Vec::new());
        }

        while self.rule_types.len() <= index as usize {
            self.rule_types.push(RuleType::Complete);
        }
        self.rule_types[index as usize] = rule_type;

        while self.rule_definition_function_params.len() <= index as usize {
            self.rule_definition_function_params.push(Vec::new());
        }

        while self.rule_definition_destructuring_patterns.len() <= index as usize {
            self.rule_definition_destructuring_patterns.push(Vec::new());
        }

        while self.rule_function_param_count.len() <= index as usize {
            self.rule_function_param_count.push(None);
        }

        while self.rule_result_registers.len() <= index as usize {
            self.rule_result_registers.push(0);
        }

        Ok(index)
    }

    fn find_module_index_for_rule(&self, rule_ref: &crate::ast::NodeRef<Rule>) -> Result<u32> {
        let rule = rule_ref.as_ref();

        for (module_idx, module) in self.policy.get_modules().iter().enumerate() {
            for policy_rule in &module.policy {
                if core::ptr::eq(policy_rule.as_ref(), rule) {
                    return Ok(module_idx as u32);
                }
            }
        }

        Ok(0)
    }

    fn find_module_package_and_index_for_rule(
        &self,
        rule_path: &str,
        rules: &Map<String, Vec<crate::ast::NodeRef<Rule>>>,
    ) -> Result<(String, u32)> {
        if let Some(rule_definitions) = rules.get(rule_path) {
            if let Some(first_rule_ref) = rule_definitions.first() {
                let rule = first_rule_ref.as_ref();

                for (module_index, module) in self.policy.get_modules().iter().enumerate() {
                    for policy_rule in &module.policy {
                        if core::ptr::eq(policy_rule.as_ref(), rule) {
                            let package_path =
                                match get_path_string(&module.package.refr, Some("data")) {
                                    Ok(path) => path,
                                    Err(e) => {
                                        return Err(CompilerError::General {
                                            message: format!(
                                                "Failed to get package path for module: {}",
                                                e
                                            ),
                                        }
                                        .into());
                                    }
                                };
                            return Ok((package_path, module_index as u32));
                        }
                    }
                }
            }
        }

        let package_components = self
            .policy
            .inner
            .rule_path_components
            .get(rule_path)
            .ok_or_else(|| CompilerError::General {
                message: format!("missing components for registered rule path '{rule_path}'"),
            })?;
        let (_, package_parts) =
            package_components
                .split_last()
                .ok_or_else(|| CompilerError::General {
                    message: format!("invalid registered rule path '{rule_path}'"),
                })?;
        let package_refs: Vec<&str> = package_parts.iter().map(String::as_str).collect();
        let package =
            format_string_path(&package_refs).map_err(|error| CompilerError::General {
                message: format!("failed to format package path for '{rule_path}': {error}"),
            })?;
        Ok((package, 0))
    }

    /// Compile from a CompiledPolicy to RVM Program.
    ///
    /// Entry-point names are canonical Rego rule paths. Use bracketed string
    /// components for literal keys that are not identifiers, such as
    /// `data.graph.defUniqueName["1.0.0"].deny`.
    pub fn compile_from_policy(
        policy: &CompiledPolicy,
        entry_points: &[&str],
    ) -> Result<Arc<Program>> {
        Self::compile_from_policy_with_host_await(policy, entry_points, &[])
    }

    /// Compile from a CompiledPolicy to RVM Program with registered host-awaitable builtins.
    pub fn compile_from_policy_with_host_await(
        policy: &CompiledPolicy,
        entry_points: &[&str],
        host_await_builtins: &[(&str, usize)],
    ) -> Result<Arc<Program>> {
        let mut compiler = Compiler::with_policy(policy);
        for &(name, arg_count) in host_await_builtins {
            compiler.register_host_await_builtin(name, arg_count)?;
        }
        compiler.current_rule_path = "".to_string();
        let rules = policy.get_rules();
        let max_components = policy
            .inner
            .rule_path_components
            .values()
            .map(Vec::len)
            .max()
            .unwrap_or_default();

        for &entry_point_name in entry_points {
            let instruction_index = compiler.program.instructions.len();
            let result_reg = compiler.alloc_register()?;
            let rule_path = if policy.inner.rule_paths.contains(entry_point_name) {
                entry_point_name.to_string()
            } else {
                let components =
                    Parser::parse_static_path_components(entry_point_name, max_components)
                        .map_err(|error| CompilerError::General {
                            message: error.to_string(),
                        })?;
                let component_refs: Vec<&str> = components.iter().map(String::as_str).collect();
                let canonical_path = format_string_path(&component_refs).map_err(|error| {
                    CompilerError::General {
                        message: error.to_string(),
                    }
                })?;
                if policy.inner.rule_paths.contains(&canonical_path) {
                    canonical_path
                } else {
                    entry_point_name.to_string()
                }
            };
            compiler
                .entry_points
                .insert(entry_point_name.to_string(), instruction_index);
            compiler.emit_entry_point_lookup(result_reg, &rule_path)?;

            compiler.emit_return(result_reg);
        }

        compiler.compile_worklist_rules(rules)?;

        let program = Arc::new(compiler.finish()?);
        Ok(program)
    }

    fn compile_worklist_rules(
        &mut self,
        rules: &Map<String, Vec<crate::ast::NodeRef<Rule>>>,
    ) -> Result<()> {
        let mut compiled_rules = BTreeSet::new();
        let mut call_stack = Vec::new();

        while !self.rule_worklist.is_empty() {
            let entry = self.rule_worklist.remove(0);

            if let Some(&target_rule_index) = self.rule_index_map.get(&entry.rule_path) {
                if entry.call_stack.contains(&target_rule_index) {
                    let mut chain = Vec::new();
                    let mut found_start = false;
                    for &rule_idx in &entry.call_stack {
                        if rule_idx == target_rule_index {
                            found_start = true;
                        }
                        if found_start {
                            if let Some((rule_path, _)) =
                                self.rule_index_map.iter().find(|(_, &idx)| idx == rule_idx)
                            {
                                chain.push(rule_path.clone());
                            }
                        }
                    }
                    chain.push(entry.rule_path.clone());

                    return Err(CompilerError::General {
                        message: format!(
                            "Compile-time recursion detected in rule call chain: {}",
                            chain.join(" -> ")
                        ),
                    }
                    .into());
                }
            }

            if compiled_rules.contains(&entry.rule_path) {
                continue;
            }

            let rule_index = if let Some(&index) = self.rule_index_map.get(&entry.rule_path) {
                index
            } else {
                return Err(CompilerError::General {
                    message: format!("Rule index not found for '{}'", entry.rule_path),
                }
                .into());
            };

            call_stack.push(entry.rule_path.clone());

            let old_rule_path = self.current_rule_path.clone();
            let old_call_stack = self.current_call_stack.clone();
            self.current_rule_path = entry.rule_path.clone();
            self.current_call_stack = entry.call_stack.clone();
            self.current_call_stack.push(rule_index);

            let result = self.compile_worklist_rule(&entry.rule_path, rules);

            self.current_rule_path = old_rule_path;
            self.current_call_stack = old_call_stack;

            call_stack.pop();

            result?;
            compiled_rules.insert(entry.rule_path);
        }
        Ok(())
    }

    fn compile_worklist_rule(
        &mut self,
        rule_path: &str,
        rules: &Map<String, Vec<crate::ast::NodeRef<Rule>>>,
    ) -> Result<()> {
        let (module_package, module_index) =
            self.find_module_package_and_index_for_rule(rule_path, rules)?;

        let saved_package = self.current_package.clone();
        let saved_module_index = self.current_module_index;
        self.current_package = module_package.clone();
        self.current_module_index = module_index;

        let saved_register_counter = self.register_counter;
        if let Some(rule_definitions) = rules.get(rule_path) {
            let Some(rule_index) = self.rule_index_map.get(rule_path).copied() else {
                return Err(CompilerError::General {
                    message: format!(
                        "Rule '{}' not found in rule index map during compilation",
                        rule_path
                    ),
                }
                .into());
            };
            let rule_type = self.rule_types[rule_index as usize].clone();

            let result_register = 0;

            while self.rule_result_registers.len() <= rule_index as usize {
                self.rule_result_registers.push(0);
            }
            self.rule_result_registers[rule_index as usize] = result_register;

            while self.rule_definitions.len() <= rule_index as usize {
                self.rule_definitions.push(Vec::new());
            }

            while self.rule_definition_function_params.len() <= rule_index as usize {
                self.rule_definition_function_params.push(Vec::new());
            }

            while self.rule_definition_destructuring_patterns.len() <= rule_index as usize {
                self.rule_definition_destructuring_patterns.push(Vec::new());
            }

            while self.rule_definition_else_bodies.len() <= rule_index as usize {
                self.rule_definition_else_bodies.push(Vec::new());
            }

            while self.rule_definition_static_values.len() <= rule_index as usize {
                self.rule_definition_static_values.push(Vec::new());
            }

            let mut num_registers_used = 0;
            let mut rule_param_count: Option<usize> = None;

            let mut contributing_definitions = Vec::new();
            for definition in rule_definitions {
                if let Some(shape) = self.definition_shape(rule_path, definition)? {
                    contributing_definitions.push((definition, shape));
                }
            }
            let shapes: Vec<_> = contributing_definitions
                .iter()
                .map(|(_, shape)| shape.clone())
                .collect();
            // `ObjectSet` overwrites, so once any definition needs a deep or
            // multi-value set, all of them use `ObjectDeepSet` to detect
            // conflicting contributions consistently.
            let deep_object_set = rule_type == RuleType::PartialObject
                && shapes.iter().any(|shape| {
                    shape.multi_value
                        || shape.keys.len() != 1
                        || !Self::static_head_prefix(shape).is_empty()
                });

            if rule_type == RuleType::PartialObject {
                let initial = Self::initial_partial_object(rule_path, &shapes)?;
                if initial != Value::new_object() {
                    let span = rule_definitions.first().unwrap().span();
                    let entry = self.program.instructions.len() as u32;
                    let literal_idx = self.add_literal(initial);
                    self.emit_instruction(
                        Instruction::Load {
                            dest: result_register,
                            literal_idx,
                        },
                        span,
                    );
                    self.emit_instruction(Instruction::RuleReturn {}, span);
                    self.rule_definitions[rule_index as usize].push(alloc::vec![entry]);
                    self.rule_definition_function_params[rule_index as usize].push(None);
                    self.rule_definition_destructuring_patterns[rule_index as usize].push(None);
                    self.rule_definition_else_bodies[rule_index as usize].push(alloc::vec![false]);
                    self.rule_definition_static_values[rule_index as usize].push(None);
                    num_registers_used = 1;
                }
            }

            for (def_idx, (rule_ref, shape)) in contributing_definitions.into_iter().enumerate() {
                if let Rule::Spec { head, bodies, span } = rule_ref.as_ref() {
                    self.push_scope();
                    self.register_counter = 0;

                    let result_register = self.alloc_register()?;

                    self.current_module_index = self.find_module_index_for_rule(rule_ref)?;
                    let module = self
                        .policy
                        .get_modules()
                        .get(self.current_module_index as usize)
                        .ok_or_else(|| CompilerError::General {
                            message: "Missing definition module".to_string(),
                        })?;
                    self.current_package = get_path_string(&module.package.refr, Some("data"))
                        .map_err(|error| CompilerError::General {
                            message: format!("Failed to get definition package: {error}"),
                        })?;

                    let (key_expr, value_expr) = match head {
                        RuleHead::Compr { assign, .. } => {
                            self.rule_definition_function_params[rule_index as usize].push(None);
                            self.rule_definition_destructuring_patterns[rule_index as usize]
                                .push(None);

                            let output_expr = assign.as_ref().map(|assign| assign.value.clone());
                            (None::<ExprRef>, output_expr)
                        }
                        RuleHead::Set { key, .. } => {
                            self.rule_definition_function_params[rule_index as usize].push(None);
                            self.rule_definition_destructuring_patterns[rule_index as usize]
                                .push(None);

                            (None, key.clone())
                        }
                        RuleHead::Func { assign, args, .. } => {
                            let mut param_names = Vec::new();
                            let mut last_param_span: Option<Span> = None;

                            let destructuring_entry = if args.is_empty() {
                                None
                            } else {
                                Some(self.program.instructions.len())
                            };

                            let param_base_register = self.register_counter;
                            self.register_counter =
                                self.register_counter.saturating_add(args.len() as u8);

                            for (arg_idx, arg) in args.iter().enumerate() {
                                let param_reg = param_base_register + arg_idx as u8;

                                let param_name = match arg.as_ref() {
                                    Expr::Var {
                                        value: Value::String(name),
                                        ..
                                    } => name.to_string(),
                                    _ => format!("__param_{}", arg_idx),
                                };
                                param_names.push(param_name);

                                let context_desc = format!("function parameter {arg_idx}");
                                let binding_plan =
                                    self.expect_binding_plan_for_expr(arg, &context_desc)?;

                                if let BindingPlan::Parameter { .. } = &binding_plan {
                                    let _ = self
                                        .apply_binding_plan(&binding_plan, param_reg, arg.span())
                                        .map_err(|e| CompilerError::from(e).at(arg.span()))?;
                                } else {
                                    return Err(CompilerError::UnexpectedBindingPlan {
                                        context: context_desc,
                                        found: format!("{binding_plan:?}"),
                                    }
                                    .at(arg.span()));
                                }

                                last_param_span = Some(arg.span().clone());
                            }

                            self.rule_definition_function_params[rule_index as usize]
                                .push(Some(param_names.clone()));

                            if let Some(entry) = destructuring_entry {
                                let success_span = last_param_span.as_ref().unwrap_or(span);
                                self.emit_instruction(
                                    crate::rvm::instructions::Instruction::DestructuringSuccess {},
                                    success_span,
                                );
                                self.rule_definition_destructuring_patterns[rule_index as usize]
                                    .push(Some(entry as u32));
                            } else {
                                self.rule_definition_destructuring_patterns[rule_index as usize]
                                    .push(None);
                            }

                            match rule_param_count {
                                None => {
                                    rule_param_count = Some(param_names.len());
                                }
                                Some(expected_count) => {
                                    if param_names.len() != expected_count {
                                        return Err(CompilerError::General {
                                            message: format!(
												"Function rule '{}' definition {} has {} parameters but expected {} parameters",
												rule_path, def_idx, param_names.len(), expected_count
											),
                                        }
                                        .at(span));
                                    }
                                }
                            }

                            match assign {
                                Some(assignment) => (None, Some(assignment.value.clone())),
                                None => (None, None),
                            }
                        }
                    };

                    let span = match (&key_expr, &value_expr) {
                        (_, Some(expr)) => expr.span().clone(),
                        (Some(expr), _) => expr.span().clone(),
                        _ => span.clone(),
                    };

                    let object_head = (rule_type == RuleType::PartialObject).then(|| ObjectHead {
                        keys: shape.keys.clone(),
                        multi_value: shape.multi_value,
                        deep: deep_object_set,
                    });
                    let context = CompilationContext {
                        dest_register: result_register,
                        context_type: ContextType::Rule(rule_type.clone()),
                        key_expr,
                        value_expr,
                        object_head,
                        value_literal: shape.value_literal.clone(),
                        span,
                        key_value_loops_hoisted: false,
                    };
                    self.push_context(context);
                    let mut body_entry_points = Vec::new();
                    let mut body_is_else = Vec::new();

                    if bodies.is_empty() {
                        let value_expr_opt = self.context_stack.last().unwrap().value_expr.clone();
                        if let Some(value_expr) = value_expr_opt {
                            let body_entry_point = self.program.instructions.len() as u32;
                            body_entry_points.push(body_entry_point);

                            self.push_scope();
                            self.reset_rule_definition_registers();

                            self.emit_instruction(
                                Instruction::RuleInit {
                                    result_reg: result_register,
                                    rule_index,
                                },
                                value_expr.span(),
                            );

                            // Loops in head keys (`p[input.keys[_]] contains 1`)
                            // must be hoisted even without a body.
                            self.hoist_loops_and_emit_context_yield()?;

                            self.emit_instruction(Instruction::RuleReturn {}, value_expr.span());
                            self.pop_scope();
                        }
                    } else {
                        for (body_idx, body) in bodies.iter().enumerate() {
                            self.push_scope();
                            self.reset_rule_definition_registers();

                            let body_entry_point = self.program.instructions.len() as u32;
                            body_entry_points.push(body_entry_point);
                            body_is_else.push(body.is_else);

                            ::core::convert::identity(body_idx);

                            let previous_value_expr = self
                                .context_stack
                                .last()
                                .and_then(|ctx| ctx.value_expr.clone());
                            let mut body_value_expr =
                                body.assign.as_ref().map(|assign| assign.value.clone());
                            if body_value_expr.is_none()
                                && (body_idx == 0
                                    || matches!(
                                        rule_type,
                                        RuleType::PartialSet | RuleType::PartialObject
                                    ))
                            {
                                body_value_expr = previous_value_expr.clone();
                            }

                            if let Some(context) = self.context_stack.last_mut() {
                                context.value_expr = body_value_expr.clone();
                            }

                            self.emit_instruction(
                                Instruction::RuleInit {
                                    result_reg: result_register,
                                    rule_index,
                                },
                                &body.span,
                            );

                            let yields_into_object = self.context_stack.last().is_some_and(|ctx| {
                                ctx.object_head.is_some() || ctx.key_expr.is_some()
                            });
                            if !body.query.stmts.is_empty() || yields_into_object {
                                self.compile_query(&body.query)?;
                            } else if let Some(value_expr) = body_value_expr.clone() {
                                let value_reg = self.compile_rego_expr(&value_expr)?;
                                self.emit_instruction(
                                    Instruction::Move {
                                        dest: result_register,
                                        src: value_reg,
                                    },
                                    value_expr.span(),
                                );
                            }

                            self.emit_instruction(Instruction::RuleReturn {}, &body.span);

                            if let Some(context) = self.context_stack.last_mut() {
                                context.value_expr = previous_value_expr;
                            }

                            self.pop_scope();
                        }
                    }

                    self.pop_scope();

                    // Compute this definition's static value for early-exit analysis.
                    // A definition has a known static value if every body (including
                    // else-branches) would produce the same literal.
                    let def_static_value = if bodies.is_empty() {
                        let head_value = self
                            .context_stack
                            .last()
                            .and_then(|ctx| ctx.value_expr.clone());
                        Self::static_value_of_expr(&head_value)
                    } else {
                        let head_value = self
                            .context_stack
                            .last()
                            .and_then(|ctx| ctx.value_expr.clone());
                        let mut consistent: Option<Value> = None;
                        let mut all_same = true;
                        for (bi, b) in bodies.iter().enumerate() {
                            let mut bve: Option<ExprRef> =
                                b.assign.as_ref().map(|a| a.value.clone());
                            if bve.is_none()
                                && (bi == 0
                                    || matches!(
                                        rule_type,
                                        RuleType::PartialSet | RuleType::PartialObject
                                    ))
                            {
                                bve = head_value.clone();
                            }
                            match Self::static_value_of_expr(&bve) {
                                Some(v) => match &consistent {
                                    None => consistent = Some(v),
                                    Some(prev) => {
                                        if *prev != v {
                                            all_same = false;
                                            break;
                                        }
                                    }
                                },
                                None => {
                                    all_same = false;
                                    break;
                                }
                            }
                        }
                        if all_same {
                            consistent
                        } else {
                            None
                        }
                    };
                    self.rule_definition_static_values[rule_index as usize].push(def_static_value);

                    self.rule_definitions[rule_index as usize].push(body_entry_points);
                    self.rule_definition_else_bodies[rule_index as usize].push(body_is_else);

                    if self.register_counter > num_registers_used {
                        num_registers_used = self.register_counter;
                    }
                }
            }

            while self.rule_num_registers.len() <= rule_index as usize {
                self.rule_num_registers.push(0);
            }
            self.rule_num_registers[rule_index as usize] = num_registers_used;

            self.rule_function_param_count[rule_index as usize] = rule_param_count;

            if rule_param_count.is_none() {
                let components = self
                    .policy
                    .inner
                    .rule_path_components
                    .get(rule_path)
                    .ok_or_else(|| CompilerError::General {
                        message: format!(
                            "missing components for registered rule path '{rule_path}'"
                        ),
                    })?;
                let (rule_name, package_parts) =
                    components
                        .split_last()
                        .ok_or_else(|| CompilerError::General {
                            message: format!("invalid registered rule path '{rule_path}'"),
                        })?;
                let package_path = package_parts.to_vec();
                let _ =
                    self.program
                        .add_rule_to_tree(&package_path, rule_name, rule_index as usize);
            }

            self.register_counter = saved_register_counter;
            self.current_package = saved_package;
            self.current_module_index = saved_module_index;
        } else {
            // Default-only rule — no body definitions to compile.
            // Ensure rule_num_registers is sized so finish() won't panic.
            if let Some(&rule_index) = self.rule_index_map.get(rule_path) {
                while self.rule_num_registers.len() <= rule_index as usize {
                    self.rule_num_registers.push(0);
                }

                // Add the rule to the data tree so it is discoverable.
                let components = self
                    .policy
                    .inner
                    .rule_path_components
                    .get(rule_path)
                    .ok_or_else(|| CompilerError::General {
                        message: format!(
                            "missing components for registered rule path '{rule_path}'"
                        ),
                    })?;
                let (rule_name, package_parts) =
                    components
                        .split_last()
                        .ok_or_else(|| CompilerError::General {
                            message: format!("invalid registered rule path '{rule_path}'"),
                        })?;
                let package_path = package_parts.to_vec();
                let _ =
                    self.program
                        .add_rule_to_tree(&package_path, rule_name, rule_index as usize);
            }

            self.register_counter = saved_register_counter;
            self.current_package = saved_package;
            self.current_module_index = saved_module_index;
        }

        Ok(())
    }
}
