// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]

//! Static provenance analysis for RVM programs.
//!
//! This module computes, at compile time, the data-path origin (provenance) for
//! every register in every rule definition.  The analysis is a single forward
//! pass over each definition's instruction range and produces:
//!
//! 1. **Register provenances** – the `input.*` / `data.*` path that flows into
//!    each register, when statically determinable.
//! 2. **Condition infos** – structured metadata for each `Guard` /
//!    `AssertEq` instruction: which registers are checked, what their
//!    provenances are, operator kind, source text, etc.
//!
//! All results are stored inside `Program` and are available for:
//! - Explanation/causality reports (replacing the runtime `ProvenanceTracker`)
//! - Unknown/assumption handling (detecting input-rooted undefineds)

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use crate::Rc;

// ---------------------------------------------------------------------------
// Provenance types
// ---------------------------------------------------------------------------

/// The root origin of a data path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProvenanceRoot {
    /// Comes from <code>input</code>.
    Input,
    /// Comes from <code>data</code> (base documents).
    Data,
    /// Result of evaluating another rule.
    RuleResult { rule_index: u16 },
    /// Virtual data document lookup.
    VirtualDocument,
}

/// A single segment in a provenance path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Segment {
    /// Static field access, e.g. `.role`.
    Field(Rc<str>),
    /// Dynamic key lookup whose value comes from a register.
    DynamicKey { register: u8 },
    /// Wildcard iteration value, e.g. `[_]`.
    Wildcard,
    /// Wildcard iteration key.
    WildcardKey,
}

/// A fully-resolved provenance path for a register value.
///
/// Example: `input.containers[_].securityContext.privileged` is represented as:
/// ```text
/// Provenance {
///     root: Input,
///     segments: [Field("containers"), Wildcard, Field("securityContext"), Field("privileged")]
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Provenance {
    pub root: ProvenanceRoot,
    pub segments: Vec<Segment>,
    /// Fully-qualified Azure Policy alias name this value was compiled from, if any.
    /// Lets a consumer map back to the alias's `defaultPath` without inverting the
    /// (lower-cased, `properties`-flattened) normalized path in `segments`.
    pub source_alias: Option<Rc<str>>,
}

impl Provenance {
    pub const fn input() -> Self {
        Self {
            root: ProvenanceRoot::Input,
            segments: Vec::new(),
            source_alias: None,
        }
    }

    pub const fn data() -> Self {
        Self {
            root: ProvenanceRoot::Data,
            segments: Vec::new(),
            source_alias: None,
        }
    }

    pub const fn rule_result(rule_index: u16) -> Self {
        Self {
            root: ProvenanceRoot::RuleResult { rule_index },
            segments: Vec::new(),
            source_alias: None,
        }
    }

    pub const fn virtual_document() -> Self {
        Self {
            root: ProvenanceRoot::VirtualDocument,
            segments: Vec::new(),
            source_alias: None,
        }
    }

    pub fn is_input_rooted(&self) -> bool {
        self.root == ProvenanceRoot::Input
    }

    pub fn is_data_rooted(&self) -> bool {
        self.root == ProvenanceRoot::Data
    }

    /// Create a new provenance by appending a static field access.
    pub fn with_field(&self, name: &str) -> Self {
        let mut segments = self.segments.clone();
        segments.push(Segment::Field(Rc::from(name)));
        Self {
            root: self.root.clone(),
            segments,
            source_alias: self.source_alias.clone(),
        }
    }

    /// Create a new provenance by appending a dynamic key lookup.
    pub fn with_dynamic_key(&self, register: u8) -> Self {
        let mut segments = self.segments.clone();
        segments.push(Segment::DynamicKey { register });
        Self {
            root: self.root.clone(),
            segments,
            source_alias: self.source_alias.clone(),
        }
    }

    /// Create a new provenance by appending a wildcard iteration (value).
    pub fn with_wildcard(&self) -> Self {
        let mut segments = self.segments.clone();
        segments.push(Segment::Wildcard);
        Self {
            root: self.root.clone(),
            segments,
            source_alias: self.source_alias.clone(),
        }
    }

    /// Create a new provenance by appending a wildcard key.
    pub fn with_wildcard_key(&self) -> Self {
        let mut segments = self.segments.clone();
        segments.push(Segment::WildcardKey);
        Self {
            root: self.root.clone(),
            segments,
            source_alias: self.source_alias.clone(),
        }
    }

    /// Create a new provenance carrying the fully-qualified alias name this value
    /// was compiled from. Attached once, at the instruction that produces the
    /// value (see `instruction_source_aliases`), then carried forward unchanged
    /// by every other `with_*` method and by `Move` propagation.
    pub fn with_source_alias(&self, alias: &str) -> Self {
        Self {
            root: self.root.clone(),
            segments: self.segments.clone(),
            source_alias: Some(Rc::from(alias)),
        }
    }
}

impl fmt::Display for Provenance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.root {
            ProvenanceRoot::Input => write!(f, "input")?,
            ProvenanceRoot::Data => write!(f, "data")?,
            ProvenanceRoot::RuleResult { rule_index } => write!(f, "rule[{rule_index}]")?,
            ProvenanceRoot::VirtualDocument => write!(f, "virtual")?,
        }
        for seg in &self.segments {
            match *seg {
                Segment::Field(ref name) => write!(f, ".{name}")?,
                Segment::DynamicKey { register } => write!(f, "[r{register}]")?,
                Segment::Wildcard => write!(f, "[_]")?,
                Segment::WildcardKey => write!(f, "[_key]")?,
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Condition info types
// ---------------------------------------------------------------------------

/// The kind of condition being asserted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConditionKind {
    /// A comparison operator (==, !=, <, <=, >, >=).
    Comparison,
    /// A membership test (`x in coll`).
    Membership,
    /// A truthiness/boolean check.
    Truthiness,
    /// An existence check (not-undefined).
    Existence,
    /// An equality assertion (`AssertEq`).
    EqualityAssertion,
    /// A variable binding (`:=` assignment).
    Binding,
    /// A structured predicate builtin (`startswith`, `endswith`, `contains(str, substr)`).
    /// Distinct from `Comparison` because comparisons dispatch through dedicated RVM
    /// opcodes with a closed `Operator` enum; builtins go through `BuiltinCall` and carry
    /// an arbitrary function name.
    Builtin,
}

/// Comparison/logical operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operator {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Contains,
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Eq => write!(f, "=="),
            Self::Ne => write!(f, "!="),
            Self::Lt => write!(f, "<"),
            Self::Le => write!(f, "<="),
            Self::Gt => write!(f, ">"),
            Self::Ge => write!(f, ">="),
            Self::Contains => write!(f, "in"),
        }
    }
}

/// Operand information for a binary condition.
#[derive(Debug, Clone)]
pub struct ConditionOperands {
    pub left_reg: u8,
    pub right_reg: u8,
    pub left_provenance: Option<Provenance>,
    pub right_provenance: Option<Provenance>,
}

/// Static metadata for a single assertion instruction.
///
/// Stored in `Program::condition_infos` parallel to the instruction vector.
#[derive(Debug, Clone)]
pub struct StaticConditionInfo {
    /// The register being checked/asserted.
    pub checked_register: u8,
    /// Provenance of the checked register (if statically known).
    pub checked_provenance: Option<Provenance>,
    /// For binary conditions: operand details.
    pub operands: Option<ConditionOperands>,
    /// Source text of the condition expression.
    pub text: String,
    /// What kind of condition this is.
    pub kind: ConditionKind,
    /// The comparison operator (for Comparison kind).
    pub operator: Option<Operator>,
    /// Whether any operand has input-rooted provenance.
    pub has_input_operand: bool,
    /// For binding conditions: the variable name being bound (e.g. `"container"`).
    pub binding_name: Option<String>,
    /// For Builtin kind: the builtin function name (e.g. `"startswith"`, `"endswith"`,
    /// `"contains"`). `None` for every other kind. Populated by `peek_preceding_builtin`
    /// when the guard register was written by a `BuiltinCall` for a whitelisted predicate.
    pub builtin_name: Option<String>,
    /// Orthogonal modifier: `true` when the condition's truth is inverted (bytecode
    /// `Not(inner)` before the branch). Applies alongside any `kind`: for example a
    /// `not X == Y` guard emits `kind: Comparison, negated: true`, and a
    /// `not startswith(X, "foo")` emits `kind: Builtin, negated: true`.
    pub negated: bool,
}

impl StaticConditionInfo {
    /// Returns true if this condition involves an input-rooted value.
    pub fn involves_input(&self) -> bool {
        self.has_input_operand
            || self
                .checked_provenance
                .as_ref()
                .is_some_and(Provenance::is_input_rooted)
    }
}

// ---------------------------------------------------------------------------
// Static analysis pass
// ---------------------------------------------------------------------------

use crate::rvm::instructions::{GuardMode, Instruction, LiteralOrRegister};
use crate::rvm::program::Program;

/// Run the static provenance analysis on a compiled program.
///
/// This populates `program.condition_infos` and `program.register_provenances`.
#[cfg(feature = "explanations")]
pub fn analyze(program: &mut Program) {
    let num_instructions = program.instructions.len();
    let mut condition_infos: Vec<Option<StaticConditionInfo>> = Vec::new();
    condition_infos.resize_with(num_instructions, || None);

    let mut all_register_provenances: Vec<Vec<Option<Provenance>>> = Vec::new();

    // Analyze each rule definition.
    for rule_info in &program.rule_infos {
        for def_body_pcs in rule_info.definitions.iter() {
            if def_body_pcs.is_empty() {
                continue;
            }

            let num_regs = usize::from(rule_info.num_registers);
            let mut reg_provenance: Vec<Option<Provenance>> = Vec::new();
            reg_provenance.resize_with(num_regs, || None);

            // Determine instruction range for this definition body.
            // The body PCs are the starting PCs of each body block within the definition.
            // Walk from the first body PC until we hit a RuleReturn.
            let first_pc = def_body_pcs.first().copied().unwrap_or(0);
            let first_pc_usize: usize = first_pc.try_into().unwrap_or(0);

            // Walk instructions from first_pc to RuleReturn.
            let mut pc = first_pc_usize;
            while pc < num_instructions {
                let instruction = program.instructions.get(pc).copied();
                let Some(instr) = instruction else {
                    break;
                };

                analyze_instruction(
                    &instr,
                    pc,
                    &mut reg_provenance,
                    &mut condition_infos,
                    program,
                );

                if matches!(instr, Instruction::RuleReturn {}) {
                    break;
                }
                pc = pc.saturating_add(1);
            }

            all_register_provenances.push(reg_provenance);
        }
    }

    // Azure Policy compiles to a flat `main` entry point with no rule structure,
    // so the loop above never runs. Walk the whole program once instead.
    if program.rule_infos.is_empty() {
        let mut reg_provenance: Vec<Option<Provenance>> = Vec::new();
        reg_provenance.resize_with(usize::from(u8::MAX) + 1, || None);
        for pc in 0..num_instructions {
            let Some(instr) = program.instructions.get(pc).copied() else {
                break;
            };
            analyze_instruction(
                &instr,
                pc,
                &mut reg_provenance,
                &mut condition_infos,
                program,
            );
        }
        all_register_provenances.push(reg_provenance);
    }

    program.condition_infos = condition_infos;
    program.register_provenances = all_register_provenances;
}

/// Describe an Azure Policy operator in the terms the causality report speaks.
///
/// `operator` is only set where a Rego equivalent exists; the AP name is always
/// carried in `builtin_name` so the author's own operator survives regardless.
///
/// Not feature-gated: `PolicyCondition` is part of the shared instruction set,
/// so its match arm compiles even when `azure_policy` is off.
fn classify_policy_op(
    op: crate::rvm::instructions::PolicyOp,
) -> (ConditionKind, Option<Operator>, Option<String>) {
    use crate::rvm::instructions::PolicyOp as P;
    let name = |s: &str| Some(String::from(s));
    match op {
        P::Equals => (
            ConditionKind::Comparison,
            Some(Operator::Eq),
            name("equals"),
        ),
        P::NotEquals => (
            ConditionKind::Comparison,
            Some(Operator::Ne),
            name("notEquals"),
        ),
        P::Greater => (
            ConditionKind::Comparison,
            Some(Operator::Gt),
            name("greater"),
        ),
        P::GreaterOrEquals => (
            ConditionKind::Comparison,
            Some(Operator::Ge),
            name("greaterOrEquals"),
        ),
        P::Less => (ConditionKind::Comparison, Some(Operator::Lt), name("less")),
        P::LessOrEquals => (
            ConditionKind::Comparison,
            Some(Operator::Le),
            name("lessOrEquals"),
        ),
        P::In => (
            ConditionKind::Membership,
            Some(Operator::Contains),
            name("in"),
        ),
        P::NotIn => (
            ConditionKind::Membership,
            Some(Operator::Contains),
            name("notIn"),
        ),
        P::Contains => (ConditionKind::Builtin, None, name("contains")),
        P::NotContains => (ConditionKind::Builtin, None, name("notContains")),
        P::ContainsKey => (ConditionKind::Builtin, None, name("containsKey")),
        P::NotContainsKey => (ConditionKind::Builtin, None, name("notContainsKey")),
        P::Like => (ConditionKind::Builtin, None, name("like")),
        P::NotLike => (ConditionKind::Builtin, None, name("notLike")),
        P::Match => (ConditionKind::Builtin, None, name("match")),
        P::NotMatch => (ConditionKind::Builtin, None, name("notMatch")),
        P::MatchInsensitively => (ConditionKind::Builtin, None, name("matchInsensitively")),
        P::NotMatchInsensitively => (ConditionKind::Builtin, None, name("notMatchInsensitively")),
        P::Exists => (ConditionKind::Existence, None, name("exists")),
        P::Not => (ConditionKind::Truthiness, None, None),
        P::ValueConditionGuard => (ConditionKind::Truthiness, None, None),
    }
}

/// Analyze a single instruction's effect on register provenances and extract
/// condition info for assertion instructions.
fn analyze_instruction(
    instr: &Instruction,
    pc: usize,
    reg_prov: &mut [Option<Provenance>],
    condition_infos: &mut [Option<StaticConditionInfo>],
    program: &Program,
) {
    use Instruction::*;

    match *instr {
        // -- Roots --
        LoadInput { dest } => {
            set_provenance(reg_prov, dest, Some(Provenance::input()));
        }
        LoadData { dest } => {
            set_provenance(reg_prov, dest, Some(Provenance::data()));
        }

        // -- Field access --
        IndexLiteral {
            dest,
            container,
            literal_idx,
        } => {
            let field_name: Option<&str> = program
                .literals
                .get(usize::from(literal_idx))
                .and_then(|v| v.as_string().ok())
                .map(|s| s.as_ref());
            let prov = get_provenance(reg_prov, container)
                .and_then(|base| field_name.map(|name| base.with_field(name)));
            set_provenance(reg_prov, dest, prov);
        }

        // -- Dynamic index --
        Index {
            dest,
            container,
            key,
        } => {
            let prov = get_provenance(reg_prov, container).map(|base| base.with_dynamic_key(key));
            set_provenance(reg_prov, dest, prov);
        }

        // -- Chained index --
        ChainedIndex { params_index } => {
            if let Some(params) = program
                .instruction_data
                .chained_index_params
                .get(usize::from(params_index))
            {
                let prov = build_chained_provenance(
                    get_provenance(reg_prov, params.root),
                    &params.path_components,
                    &program.literals,
                );
                // Fold in the FQ Azure Policy alias name, if the compiler tagged this
                // instruction as the one producing an aliased value (see
                // `Program::instruction_source_aliases`). Consulted exactly once, here,
                // at the instruction that builds the value's `Provenance` — after this,
                // `source_alias` rides along for free via `Move`/`with_field`/etc.
                let prov = match program
                    .instruction_source_aliases
                    .get(pc)
                    .and_then(Option::as_deref)
                {
                    Some(alias) => prov.map(|p| p.with_source_alias(alias)),
                    None => prov,
                };
                set_provenance(reg_prov, params.dest, prov);
            }
        }

        // -- Move / copy --
        Move { dest, src } => {
            let prov = get_provenance(reg_prov, src).cloned();
            set_provenance(reg_prov, dest, prov);

            // If this Move is a binding (`:=`), create a condition info entry.
            if let Some(binding_name) = program.binding_infos.get(pc).and_then(|b| b.clone()) {
                let checked_provenance = get_provenance(reg_prov, dest).cloned();
                let has_input = checked_provenance
                    .as_ref()
                    .is_some_and(Provenance::is_input_rooted);
                let text = get_condition_text(pc, program);
                if let Some(slot) = condition_infos.get_mut(pc) {
                    *slot = Some(StaticConditionInfo {
                        checked_register: dest,
                        checked_provenance,
                        operands: None,
                        text,
                        kind: ConditionKind::Binding,
                        operator: None,
                        has_input_operand: has_input,
                        binding_name: Some(binding_name),
                        builtin_name: None,
                        negated: false,
                    });
                }
            }
        }

        // -- Loops --
        LoopStart { params_index } => {
            if let Some(params) = program
                .instruction_data
                .loop_params
                .get(usize::from(params_index))
            {
                let base = get_provenance(reg_prov, params.collection);
                // No-suffix wildcard alias case (e.g. comparing array elements directly):
                // there is no ChainedIndex to tag, so the alias is folded in here instead,
                // at the instruction that gives the loop element its `Provenance`.
                let alias = program
                    .instruction_source_aliases
                    .get(pc)
                    .and_then(Option::as_deref);
                let val_prov = base.map(|b| {
                    let v = b.with_wildcard();
                    match alias {
                        Some(a) => v.with_source_alias(a),
                        None => v,
                    }
                });
                let key_prov = base.map(|b| b.with_wildcard_key());
                set_provenance(reg_prov, params.value_reg, val_prov);
                set_provenance(reg_prov, params.key_reg, key_prov);
                // result_reg is not given provenance here — it accumulates results
                clear_provenance(reg_prov, params.result_reg);
            }
        }

        // -- Comprehensions --
        ComprehensionBegin { params_index } => {
            if let Some(params) = program
                .instruction_data
                .comprehension_begin_params
                .get(usize::from(params_index))
            {
                let base = get_provenance(reg_prov, params.collection_reg);
                let val_prov = base.map(|b| b.with_wildcard());
                let key_prov = base.map(|b| b.with_wildcard_key());
                set_provenance(reg_prov, params.value_reg, val_prov);
                set_provenance(reg_prov, params.key_reg, key_prov);
                clear_provenance(reg_prov, params.result_reg);
            }
        }

        // -- Rule calls --
        CallRule { dest, rule_index } => {
            set_provenance(reg_prov, dest, Some(Provenance::rule_result(rule_index)));
        }

        // -- Virtual data document --
        VirtualDataDocumentLookup { params_index } => {
            if let Some(params) = program
                .instruction_data
                .virtual_data_document_lookup_params
                .get(usize::from(params_index))
            {
                set_provenance(reg_prov, params.dest, Some(Provenance::virtual_document()));
            }
        }

        // -- Assertions --
        Guard { register, mode } => {
            let info = build_guard_condition_info(register, mode, pc, reg_prov, program);
            if let Some(ci) = condition_infos.get_mut(pc) {
                *ci = Some(info);
            }
        }

        AssertEq { left, right } => {
            let info = build_assert_eq_condition_info(left, right, pc, reg_prov, program);
            if let Some(ci) = condition_infos.get_mut(pc) {
                *ci = Some(info);
            }
        }

        // -- Everything else: clear provenance on dest register --
        RuleInit { result_reg, .. } => {
            clear_provenance(reg_prov, result_reg);
        }
        Load { dest, .. }
        | LoadTrue { dest }
        | LoadFalse { dest }
        | LoadNull { dest }
        | LoadBool { dest, .. }
        | LoadContext { dest }
        | LoadMetadata { dest } => {
            clear_provenance(reg_prov, dest);
        }
        Add { dest, .. }
        | Sub { dest, .. }
        | Mul { dest, .. }
        | Div { dest, .. }
        | Mod { dest, .. } => {
            clear_provenance(reg_prov, dest);
        }
        Eq { dest, .. }
        | Ne { dest, .. }
        | Lt { dest, .. }
        | Le { dest, .. }
        | Gt { dest, .. }
        | Ge { dest, .. } => {
            clear_provenance(reg_prov, dest);
        }
        And { dest, .. } | Or { dest, .. } | Not { dest, .. } => {
            clear_provenance(reg_prov, dest);
        }
        Contains { dest, .. } | Count { dest, .. } => {
            clear_provenance(reg_prov, dest);
        }
        ArrayNew { dest } | SetNew { dest } => {
            clear_provenance(reg_prov, dest);
        }
        HostAwait { dest, .. } => {
            clear_provenance(reg_prov, dest);
        }
        Return { .. } => {}
        BuiltinCall { params_index } => {
            if let Some(params) = program
                .instruction_data
                .builtin_call_params
                .get(usize::from(params_index))
            {
                clear_provenance(reg_prov, params.dest);
            }
        }
        FunctionCall { params_index } => {
            if let Some(params) = program
                .instruction_data
                .function_call_params
                .get(usize::from(params_index))
            {
                clear_provenance(reg_prov, params.dest);
            }
        }
        ObjectCreate { params_index } => {
            if let Some(params) = program
                .instruction_data
                .object_create_params
                .get(usize::from(params_index))
            {
                clear_provenance(reg_prov, params.dest);
            }
        }
        ArrayCreate { params_index } => {
            if let Some(params) = program
                .instruction_data
                .array_create_params
                .get(usize::from(params_index))
            {
                clear_provenance(reg_prov, params.dest);
            }
        }
        SetCreate { params_index } => {
            if let Some(params) = program
                .instruction_data
                .set_create_params
                .get(usize::from(params_index))
            {
                clear_provenance(reg_prov, params.dest);
            }
        }

        // Mutation / control-flow — no dest register to clear.
        ObjectSet { .. }
        | ObjectDeepSet { .. }
        | ArrayPush { .. }
        | ArrayPushDefined { .. }
        | SetAdd { .. }
        | LoopNext { .. }
        | RuleReturn {}
        | Halt {}
        | DestructuringSuccess {}
        | ComprehensionYield { .. }
        | ComprehensionEnd {}
        | ReturnUndefinedIfNotTrue { .. }
        | CoalesceUndefinedToNull { .. }
        | LogicalBlockStart { .. }
        | AllOfNext { .. }
        | AnyOfNext { .. }
        | LogicalBlockEnd { .. }
        | NegationBegin {} => {}

        // Azure Policy condition op writes its result into `dest`.
        PolicyCondition {
            dest,
            left,
            right,
            op,
        } => {
            use crate::rvm::instructions::PolicyOp;
            let (kind, operator, builtin_name) = classify_policy_op(op);
            // Unary ops leave `right` unused; reporting it would invent an
            // expected value the policy never wrote.
            let unary = matches!(op, PolicyOp::Not | PolicyOp::Exists);
            let left_prov = get_provenance(reg_prov, left).cloned();
            let right_prov = if unary {
                None
            } else {
                get_provenance(reg_prov, right).cloned()
            };
            let has_input = left_prov.as_ref().is_some_and(Provenance::is_input_rooted)
                || right_prov.as_ref().is_some_and(Provenance::is_input_rooted);
            if let Some(slot) = condition_infos.get_mut(pc) {
                *slot = Some(StaticConditionInfo {
                    checked_register: dest,
                    checked_provenance: left_prov.clone(),
                    operands: if unary {
                        None
                    } else {
                        Some(ConditionOperands {
                            left_reg: left,
                            right_reg: right,
                            left_provenance: left_prov,
                            right_provenance: right_prov,
                        })
                    },
                    text: get_condition_text(pc, program),
                    kind,
                    operator,
                    has_input_operand: has_input,
                    binding_name: None,
                    builtin_name,
                    negated: op.is_negated(),
                });
            }
            clear_provenance(reg_prov, dest);
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn set_provenance(reg_prov: &mut [Option<Provenance>], reg: u8, prov: Option<Provenance>) {
    if let Some(slot) = reg_prov.get_mut(usize::from(reg)) {
        *slot = prov;
    }
}

fn clear_provenance(reg_prov: &mut [Option<Provenance>], reg: u8) {
    set_provenance(reg_prov, reg, None);
}

fn get_provenance(reg_prov: &[Option<Provenance>], reg: u8) -> Option<&Provenance> {
    reg_prov.get(usize::from(reg)).and_then(Option::as_ref)
}

/// Build provenance for a chained index operation by walking each path component.
fn build_chained_provenance(
    base: Option<&Provenance>,
    components: &[LiteralOrRegister],
    literals: &[crate::value::Value],
) -> Option<Provenance> {
    let mut current = base?.clone();
    for component in components {
        current = match *component {
            LiteralOrRegister::Literal(idx) => {
                let field_name: Option<&str> = literals
                    .get(usize::from(idx))
                    .and_then(|v| v.as_string().ok())
                    .map(|s| s.as_ref());
                match field_name {
                    Some(name) => current.with_field(name),
                    None => return None,
                }
            }
            LiteralOrRegister::Register(reg) => current.with_dynamic_key(reg),
        };
    }
    Some(current)
}

/// Extract source text for the condition at `pc` from span info.
fn get_condition_text(pc: usize, program: &Program) -> String {
    let span_info = match program.instruction_spans.get(pc) {
        Some(Some(info)) => info,
        _ => return String::new(),
    };

    let source = match program.sources.get(span_info.source_index) {
        Some(s) => &s.content,
        None => return String::new(),
    };

    source
        .lines()
        .nth(span_info.line.saturating_sub(1))
        .map(str::trim)
        .map(String::from)
        .unwrap_or_default()
}

/// Peek at the instruction before `pc` to identify comparison operands.
fn peek_preceding_comparison(
    pc: usize,
    reg_prov: &[Option<Provenance>],
    program: &Program,
) -> Option<(Operator, ConditionOperands)> {
    let target_dest = get_guard_register_at(pc, program)?;
    find_comparison_writing_to(pc, target_dest, reg_prov, program)
}

/// For string-predicate builtins with structured operands, return
/// `(subject_arg_idx, value_arg_idx)` — which register slot in `params.args`
/// carries the "subject" (the operand being tested, whose provenance a
/// consumer wants to attribute the failure to) and which carries the "value"
/// (the constraint literal or comparison target).
///
/// Consumers of the causality report get a uniform shape regardless of the
/// builtin's source-code arg order: `left` is always subject with provenance,
/// `right` is always value. Callers on both the static side
/// ([`peek_preceding_builtin`]) and the runtime PE side
/// (`record_builtin_assumption`) share this mapping so their emitted records
/// agree.
///
/// Returns `None` for builtins outside the whitelist below. The whitelist is
/// deliberately narrow: it covers the predicates whose arguments map cleanly
/// onto a subject/value pair, which is what makes the uniform `left`/`right`
/// shape meaningful.
#[cfg(feature = "explanations")]
pub(crate) fn builtin_operand_indices(name: &str) -> Option<(usize, usize)> {
    match name {
        // Tier 1: arg[0] = subject, arg[1] = value/pattern.
        "startswith"
        | "endswith"
        | "contains"
        | "strings.any_prefix_match"
        | "strings.any_suffix_match" => Some((0, 1)),
        // Tier 2: arg[0] = value/pattern, arg[1] = subject.
        // Rego convention puts the pattern first for regex.* and CIDR checks.
        "regex.match" | "net.cidr_contains" => Some((1, 0)),
        _ => None,
    }
}

/// Scan backward from `pc` (exclusive) looking for a comparison-like
/// instruction whose `dest` register matches `target_dest`.  Stops at the
/// nearest such instruction.  Used both for direct comparisons preceding a
/// `Guard`, and (indirectly via [`peek_through_negation`]) for the operand
/// of a `Not` instruction in `not <comparison>` patterns.
fn find_comparison_writing_to(
    pc: usize,
    target_dest: u8,
    reg_prov: &[Option<Provenance>],
    program: &Program,
) -> Option<(Operator, ConditionOperands)> {
    // Walk back a short window — comparisons that feed a Guard are emitted
    // adjacent in the same basic block, so a small bound suffices and keeps
    // the analysis cheap.
    const LOOKBACK: usize = 8;
    let start = pc.saturating_sub(LOOKBACK).max(1);
    let mut cur = pc;
    while cur > start {
        cur = cur.saturating_sub(1);
        let instr = program.instructions.get(cur)?;
        match *instr {
            Instruction::Eq { dest, left, right }
            | Instruction::Ne { dest, left, right }
            | Instruction::Lt { dest, left, right }
            | Instruction::Le { dest, left, right }
            | Instruction::Gt { dest, left, right }
            | Instruction::Ge { dest, left, right }
                if dest == target_dest =>
            {
                let op = match *instr {
                    Instruction::Eq { .. } => Operator::Eq,
                    Instruction::Ne { .. } => Operator::Ne,
                    Instruction::Lt { .. } => Operator::Lt,
                    Instruction::Le { .. } => Operator::Le,
                    Instruction::Gt { .. } => Operator::Gt,
                    Instruction::Ge { .. } => Operator::Ge,
                    _ => return None,
                };
                return Some((
                    op,
                    ConditionOperands {
                        left_reg: left,
                        right_reg: right,
                        left_provenance: get_provenance(reg_prov, left).cloned(),
                        right_provenance: get_provenance(reg_prov, right).cloned(),
                    },
                ));
            }
            Instruction::Contains {
                dest,
                collection,
                value,
            } if dest == target_dest => {
                return Some((
                    Operator::Contains,
                    ConditionOperands {
                        left_reg: value,
                        right_reg: collection,
                        left_provenance: get_provenance(reg_prov, value).cloned(),
                        right_provenance: get_provenance(reg_prov, collection).cloned(),
                    },
                ));
            }
            _ => {}
        }
    }
    None
}

/// Peek at the instruction before `pc` to identify a whitelisted string-builtin
/// call and its structured operands.  Mirrors [`peek_preceding_comparison`]
/// but for `Instruction::BuiltinCall` — see [`builtin_operand_indices`] for
/// the whitelist.  Returns `(builtin_name, operands)` where operands are
/// normalized so `left` is always the subject and `right` is always the
/// value/pattern, regardless of the builtin's source-level arg order.
#[cfg(feature = "explanations")]
fn peek_preceding_builtin(
    pc: usize,
    reg_prov: &[Option<Provenance>],
    program: &Program,
) -> Option<(String, ConditionOperands)> {
    let target_dest = get_guard_register_at(pc, program)?;
    find_builtin_writing_to(pc, target_dest, reg_prov, program)
}

/// Scan backward from `pc` (exclusive) looking for a `BuiltinCall` whose
/// `params.dest` matches `target_dest` AND whose builtin name is on the
/// whitelist. Same short-window lookback as [`find_comparison_writing_to`];
/// bails early on unrelated writes only if the scan window is exceeded.
#[cfg(feature = "explanations")]
fn find_builtin_writing_to(
    pc: usize,
    target_dest: u8,
    reg_prov: &[Option<Provenance>],
    program: &Program,
) -> Option<(String, ConditionOperands)> {
    const LOOKBACK: usize = 8;
    let start = pc.saturating_sub(LOOKBACK).max(1);
    let mut cur = pc;
    while cur > start {
        cur = cur.saturating_sub(1);
        let instr = program.instructions.get(cur)?;
        if let Instruction::BuiltinCall { params_index } = *instr {
            let params = program
                .instruction_data
                .builtin_call_params
                .get(usize::from(params_index))?;
            if params.dest != target_dest {
                continue;
            }
            let builtin_info = program
                .builtin_info_table
                .get(usize::from(params.builtin_index))?;
            let (subject_idx, value_idx) = builtin_operand_indices(&builtin_info.name)?;
            let args = params.arg_registers();
            let subject_reg = *args.get(subject_idx)?;
            let value_reg = *args.get(value_idx)?;
            return Some((
                builtin_info.name.clone(),
                ConditionOperands {
                    left_reg: subject_reg,
                    right_reg: value_reg,
                    left_provenance: get_provenance(reg_prov, subject_reg).cloned(),
                    right_provenance: get_provenance(reg_prov, value_reg).cloned(),
                },
            ));
        }
    }
    None
}

/// If the instruction immediately preceding `pc` is `Not { dest, operand }`
/// where `dest` is the register being guarded at `pc`, look further back to
/// the comparison/contains/builtin call that produced `operand`.
///
/// Returns the inner condition's structure plus the provenance of the
/// inner operand (used for `not <builtin>(...)` style negations where there
/// is no structured operator but we still want input attribution).
fn peek_through_negation(
    pc: usize,
    reg_prov: &[Option<Provenance>],
    program: &Program,
) -> Option<NegationLookThrough> {
    if pc == 0 {
        return None;
    }
    let guard_reg = get_guard_register_at(pc, program)?;
    let prev = program.instructions.get(pc.saturating_sub(1))?;
    let (not_dest, not_operand) = match *prev {
        Instruction::Not { dest, operand } if dest == guard_reg => (dest, operand),
        _ => return None,
    };
    let _ = not_dest; // already validated above

    // Case A: `not <comparison>` — inner is a comparison writing to `not_operand`.
    if let Some((op, operands)) =
        find_comparison_writing_to(pc.saturating_sub(1), not_operand, reg_prov, program)
    {
        return Some(NegationLookThrough {
            operator: Some(op),
            operands: Some(operands),
            inner_provenance: get_provenance(reg_prov, not_operand).cloned(),
            builtin_name: None,
        });
    }

    // Case B: `not <builtin>(...)` — inner is a BuiltinCall.  For whitelisted
    // string-predicate builtins (see `builtin_operand_indices`), synthesize
    // structured `left`/`right` operands + propagate the builtin name so the
    // outer `kind: Negation` record carries the same shape as an un-negated
    // builtin.  For non-whitelisted builtins, fall back to today's behavior:
    // attach only the first input-rooted argument's provenance so callers can
    // still attribute the failure to the right input path.
    let lookback_start = pc.saturating_sub(8).max(1);
    let mut cur = pc.saturating_sub(1);
    while cur > lookback_start {
        cur = cur.saturating_sub(1);
        let candidate = program.instructions.get(cur)?;
        if let Instruction::BuiltinCall { params_index } = *candidate {
            if let Some(params) = program
                .instruction_data
                .builtin_call_params
                .get(usize::from(params_index))
            {
                if params.dest == not_operand {
                    let builtin_info = program
                        .builtin_info_table
                        .get(usize::from(params.builtin_index));

                    // Try whitelisted structured shape first.
                    if let Some(info) = builtin_info {
                        if let Some((subject_idx, value_idx)) = builtin_operand_indices(&info.name)
                        {
                            let args = params.arg_registers();
                            if let (Some(&subject_reg), Some(&value_reg)) =
                                (args.get(subject_idx), args.get(value_idx))
                            {
                                let operands = ConditionOperands {
                                    left_reg: subject_reg,
                                    right_reg: value_reg,
                                    left_provenance: get_provenance(reg_prov, subject_reg).cloned(),
                                    right_provenance: get_provenance(reg_prov, value_reg).cloned(),
                                };
                                let inner_prov = get_provenance(reg_prov, subject_reg)
                                    .or_else(|| get_provenance(reg_prov, not_operand))
                                    .cloned();
                                return Some(NegationLookThrough {
                                    operator: None,
                                    operands: Some(operands),
                                    inner_provenance: inner_prov,
                                    builtin_name: Some(info.name.clone()),
                                });
                            }
                        }
                    }

                    // Fallback: non-whitelisted builtin. Preserve today's
                    // behavior — surface only the first input-rooted arg's
                    // provenance so consumers can still attribute the input.
                    let inner_prov = params
                        .arg_registers()
                        .iter()
                        .find_map(|reg| {
                            get_provenance(reg_prov, *reg)
                                .filter(|p| p.is_input_rooted())
                                .cloned()
                        })
                        .or_else(|| get_provenance(reg_prov, not_operand).cloned());
                    return Some(NegationLookThrough {
                        operator: None,
                        operands: None,
                        inner_provenance: inner_prov,
                        builtin_name: None,
                    });
                }
            }
        }
    }

    get_provenance(reg_prov, not_operand)
        .filter(|provenance| provenance.is_input_rooted() || provenance.is_data_rooted())
        .cloned()
        .map(|provenance| NegationLookThrough {
            operator: None,
            operands: None,
            inner_provenance: Some(provenance),
            builtin_name: None,
        })
}

/// Result of looking through a `Not` instruction at the source condition.
struct NegationLookThrough {
    operator: Option<Operator>,
    operands: Option<ConditionOperands>,
    inner_provenance: Option<Provenance>,
    /// For `not <whitelisted-builtin>(...)`: the inner builtin's name so
    /// callers can propagate `builtin_name` onto the outer Negation-kind
    /// `StaticConditionInfo`. `None` for `not <comparison>` and for
    /// non-whitelisted builtins.
    builtin_name: Option<String>,
}

/// Get the register being checked by the Guard instruction at `pc`.
fn get_guard_register_at(pc: usize, program: &Program) -> Option<u8> {
    let instr = program.instructions.get(pc).copied()?;
    match instr {
        Instruction::Guard { register, .. } => Some(register),
        _ => None,
    }
}

fn build_guard_condition_info(
    register: u8,
    mode: GuardMode,
    pc: usize,
    reg_prov: &[Option<Provenance>],
    program: &Program,
) -> StaticConditionInfo {
    let checked_provenance = get_provenance(reg_prov, register).cloned();
    let text = get_condition_text(pc, program);

    match mode {
        GuardMode::Condition => {
            // Try to find the comparison that produced this boolean.
            if let Some((op, operands)) = peek_preceding_comparison(pc, reg_prov, program) {
                let has_input = operands
                    .left_provenance
                    .as_ref()
                    .is_some_and(Provenance::is_input_rooted)
                    || operands
                        .right_provenance
                        .as_ref()
                        .is_some_and(Provenance::is_input_rooted);
                // Use the input-rooted operand's provenance as checked_provenance
                // (the guard register itself holds a boolean, not the input path).
                let effective_provenance = if has_input {
                    operands
                        .left_provenance
                        .as_ref()
                        .filter(|p| p.is_input_rooted())
                        .or(operands
                            .right_provenance
                            .as_ref()
                            .filter(|p| p.is_input_rooted()))
                        .cloned()
                } else {
                    checked_provenance
                };
                StaticConditionInfo {
                    checked_register: register,
                    checked_provenance: effective_provenance,
                    operands: Some(operands),
                    text,
                    kind: ConditionKind::Comparison,
                    operator: Some(op),
                    has_input_operand: has_input,
                    binding_name: None,
                    builtin_name: None,
                    negated: false,
                }
            } else if let Some((name, operands)) = peek_preceding_builtin(pc, reg_prov, program) {
                // `startswith(x, "y")` / `endswith` / `contains` / `regex.match` /
                // `net.cidr_contains` / `strings.any_{prefix,suffix}_match` —
                // Guard fires on the boolean result of a whitelisted string
                // predicate builtin (see `builtin_operand_indices`). Emit
                // structured operands + builtin_name so the causality report
                // renders identically to a comparison and a consumer can key
                // on (kind: "builtin", builtin_name).
                let has_input = operands
                    .left_provenance
                    .as_ref()
                    .is_some_and(Provenance::is_input_rooted)
                    || operands
                        .right_provenance
                        .as_ref()
                        .is_some_and(Provenance::is_input_rooted);
                let effective_provenance = if has_input {
                    operands
                        .left_provenance
                        .as_ref()
                        .filter(|p| p.is_input_rooted())
                        .or(operands
                            .right_provenance
                            .as_ref()
                            .filter(|p| p.is_input_rooted()))
                        .cloned()
                } else {
                    checked_provenance
                };
                StaticConditionInfo {
                    checked_register: register,
                    checked_provenance: effective_provenance,
                    operands: Some(operands),
                    text,
                    kind: ConditionKind::Builtin,
                    operator: None,
                    has_input_operand: has_input,
                    binding_name: None,
                    builtin_name: Some(name),
                    negated: false,
                }
            } else if let Some(neg) = peek_through_negation(pc, reg_prov, program) {
                // `not <expr>` — Guard fires on `Not(inner)`.  Surface the
                // inner expression's operator / operand provenance so the
                // condition carries the same structured attribution as the
                // un-negated form, but marked as Negation so consumers know
                // the outcome is inverted.
                let has_input = neg
                    .operands
                    .as_ref()
                    .map(|ops| {
                        ops.left_provenance
                            .as_ref()
                            .is_some_and(Provenance::is_input_rooted)
                            || ops
                                .right_provenance
                                .as_ref()
                                .is_some_and(Provenance::is_input_rooted)
                    })
                    .unwrap_or_else(|| {
                        neg.inner_provenance
                            .as_ref()
                            .is_some_and(Provenance::is_input_rooted)
                    });
                let effective_provenance = if has_input {
                    neg.operands
                        .as_ref()
                        .and_then(|ops| {
                            ops.left_provenance
                                .as_ref()
                                .filter(|p| p.is_input_rooted())
                                .or(ops
                                    .right_provenance
                                    .as_ref()
                                    .filter(|p| p.is_input_rooted()))
                                .cloned()
                        })
                        .or_else(|| neg.inner_provenance.clone())
                } else {
                    neg.inner_provenance.clone().or(checked_provenance)
                };

                // For `not <builtin>(...)` (operator is None) the look-through
                // doesn't synthesize structured operands; fall back to a
                // single-operand frame that still carries the inner
                // provenance so the rendered `left` operand can attribute
                // the failure to the right input path.
                let operands = neg.operands.or_else(|| {
                    neg.inner_provenance.clone().map(|prov| ConditionOperands {
                        left_reg: register,
                        right_reg: register,
                        left_provenance: Some(prov),
                        right_provenance: None,
                    })
                });

                // Negation is an orthogonal modifier, so derive the outer
                // `kind` from what `peek_through_negation` recovered:
                //   - whitelisted builtin  → kind: Builtin  (Case B success)
                //   - bare comparison      → kind: Comparison (Case A)
                //   - opaque (non-whitelisted builtin or no inner) → kind: Truthiness
                // In all three cases, `negated: true` flags the inversion.
                let inferred_kind = if neg.builtin_name.is_some() {
                    ConditionKind::Builtin
                } else if neg.operator.is_some() {
                    ConditionKind::Comparison
                } else {
                    ConditionKind::Truthiness
                };
                StaticConditionInfo {
                    checked_register: register,
                    checked_provenance: effective_provenance,
                    operands,
                    text,
                    kind: inferred_kind,
                    operator: neg.operator,
                    has_input_operand: has_input,
                    binding_name: None,
                    builtin_name: neg.builtin_name,
                    negated: true,
                }
            } else {
                // Generic truthiness guard.
                let has_input = checked_provenance
                    .as_ref()
                    .is_some_and(Provenance::is_input_rooted);
                StaticConditionInfo {
                    checked_register: register,
                    checked_provenance,
                    operands: None,
                    text,
                    kind: ConditionKind::Truthiness,
                    operator: None,
                    has_input_operand: has_input,
                    binding_name: None,
                    builtin_name: None,
                    negated: false,
                }
            }
        }
        GuardMode::NotUndefined => {
            let has_input = checked_provenance
                .as_ref()
                .is_some_and(Provenance::is_input_rooted);
            StaticConditionInfo {
                checked_register: register,
                checked_provenance,
                operands: None,
                text,
                kind: ConditionKind::Existence,
                operator: None,
                has_input_operand: has_input,
                binding_name: None,
                builtin_name: None,
                negated: false,
            }
        }
        GuardMode::Not => {
            // Opaque negation (no structured inner recovered): emit as
            // Truthiness with `negated: true`, matching the else-branch above.
            let has_input = checked_provenance
                .as_ref()
                .is_some_and(Provenance::is_input_rooted);
            StaticConditionInfo {
                checked_register: register,
                checked_provenance,
                operands: None,
                text,
                kind: ConditionKind::Truthiness,
                operator: None,
                has_input_operand: has_input,
                binding_name: None,
                builtin_name: None,
                negated: true,
            }
        }
    }
}

fn build_assert_eq_condition_info(
    left: u8,
    right: u8,
    pc: usize,
    reg_prov: &[Option<Provenance>],
    program: &Program,
) -> StaticConditionInfo {
    let left_prov = get_provenance(reg_prov, left).cloned();
    let right_prov = get_provenance(reg_prov, right).cloned();
    let text = get_condition_text(pc, program);
    let has_input = left_prov.as_ref().is_some_and(Provenance::is_input_rooted)
        || right_prov.as_ref().is_some_and(Provenance::is_input_rooted);
    StaticConditionInfo {
        checked_register: left, // Convention: left is the "checked" side
        checked_provenance: left_prov.clone(),
        operands: Some(ConditionOperands {
            left_reg: left,
            right_reg: right,
            left_provenance: left_prov,
            right_provenance: right_prov,
        }),
        text,
        kind: ConditionKind::EqualityAssertion,
        operator: Some(Operator::Eq),
        has_input_operand: has_input,
        binding_name: None,
        builtin_name: None,
        negated: false,
    }
}

#[cfg(test)]
mod tests {
    use super::get_condition_text;
    use crate::rvm::program::{Program, SourceFile, SpanInfo};

    #[test]
    fn get_condition_text_returns_full_trimmed_line() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "package test\n        some link in input.links\n".into(),
        ));
        program
            .instruction_spans
            .push(Some(SpanInfo::new(0, 2, 23, 4)));

        let text = get_condition_text(0, &program);

        assert_eq!(text, "some link in input.links");
    }

    // Step 6 (Azure Policy attribution): `source_alias` must survive being
    // carried forward exactly the way the rest of `Provenance` already does
    // across a `Move` (a variable binding). The `Move` arm in `analyze()`
    // clones the whole `Provenance` verbatim (`get_provenance(...).cloned()`),
    // so this is a type-level guarantee -- proven here directly on
    // `Provenance`, since reproducing a full Azure Policy count-binding
    // fixture (the compiler construct that actually emits such a `Move`) is
    // a separate, not-yet-read investigation (see the parent plan's Step 6,
    // sub-step 5). A full end-to-end test through that construct remains a
    // follow-up; this proves the mechanism the follow-up would rely on.
    #[test]
    fn source_alias_survives_field_appends_and_a_clone_carrying_move() {
        use super::Provenance;

        let base =
            Provenance::input().with_source_alias("Microsoft.Storage/storageAccounts/accessTier");

        // Simulates further path-building after the alias was attached --
        // e.g. a nested property read off an aliased object.
        let extended = base.with_field("nested");
        assert_eq!(
            extended.source_alias.as_deref(),
            Some("Microsoft.Storage/storageAccounts/accessTier"),
            "with_field must not drop source_alias"
        );

        // Simulates exactly what the `Move` arm in `analyze()` does:
        // `get_provenance(reg_prov, src).cloned()` then `set_provenance(dest, ...)`.
        let moved: Provenance = extended.clone();
        assert_eq!(
            moved.source_alias, extended.source_alias,
            "a Move's plain .cloned() must carry source_alias forward unchanged"
        );
    }
}
