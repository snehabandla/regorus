// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Static provenance of the checks in a compiled RVM [`Program`].
//!
//! [`Provenance`] decodes, once per program and without running it, every
//! instruction that checks a condition: its policy text and location, its
//! [`ConditionKind`] and [`Operator`], the references its operands were read
//! from, and the rule or function that owns it. Explanation capture records
//! only program counters; reports resolve them through this table.
//!
//! Only programs compiled from Rego are decoded. A program without rule
//! information, such as one compiled from Azure Policy, has no sites, so
//! its conditions and its reads of the `context` root are not described.

use super::report::{ConditionKind, Operator, RuleKind, SourceLocation};
use crate::rvm::instructions::{GuardMode, Instruction};
use crate::rvm::program::{Program, SpanInfo};
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

/// Identifies a [`CheckSite`] within its [`Provenance`].
///
/// Sites are numbered from 0 in program order, so compiling the same policy
/// with the same entry points gives the same ids. Explanations refer to a
/// check by id instead of repeating its text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SiteId(pub u32);

/// The rule body or function definition that a check belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConditionOwner {
    /// Index of the rule; see [`Provenance::rule`].
    pub rule: usize,
    /// Index of the rule definition.
    pub definition: usize,
    /// Index of the body within the definition (`else` bodies count), or
    /// `None` for the matching of a function's arguments.
    pub body: Option<usize>,
}

/// A rule or function of the program.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct RuleOwner {
    /// Full path of the rule, for example `data.test.allow`.
    pub name: String,
    /// Kind of the rule.
    pub kind: RuleKind,
}

/// An instruction that checks a condition.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct CheckSite {
    /// Id of the site.
    pub id: SiteId,
    /// Program counter of the checking instruction.
    pub pc: usize,
    /// Rule body that the check belongs to.
    pub owner: ConditionOwner,
    /// Position of the check among the checks of its owner body, from 0.
    /// With the owner's rule name, definition and body, this identifies
    /// the check independently of the other rules in the program.
    pub ordinal: usize,
    /// Kind of condition.
    pub kind: ConditionKind,
    /// Operator of a comparison or membership test.
    pub operator: Option<Operator>,
    /// The checked expression as written in the policy.
    pub text: String,
    /// Where the checked expression starts.
    pub location: Option<SourceLocation>,
    /// Reference the left operand (or the checked value) was read from, as
    /// written, for example `input.user.role`. A value bound by iteration
    /// reads as the collection followed by `[_]`, for example
    /// `input.items[_]`. `None` for literals and computed values.
    pub left_path: Option<String>,
    /// Reference the right operand was read from, as for `left_path`.
    pub right_path: Option<String>,
}

/// Static provenance of every check in a program. See the module docs.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Provenance {
    rules: Vec<RuleOwner>,
    sites: Vec<CheckSite>,
}

impl Provenance {
    /// Decodes the checks of `program`.
    pub fn new(program: &Program) -> Self {
        let sources: Vec<SourceIndex> = program
            .sources
            .iter()
            .map(|source| SourceIndex::new(&source.content))
            .collect();
        let rules = program
            .rule_infos
            .iter()
            .map(|info| RuleOwner {
                name: info.name.clone(),
                kind: if info.function_info.is_some() {
                    RuleKind::Function
                } else {
                    RuleKind::from(info.rule_type.clone())
                },
            })
            .collect();
        let owners = owner_starts(program);
        let mut sites: Vec<CheckSite> = Vec::new();
        let mut ordinal = 0_usize;
        let mut previous_owner = None;
        for (pc, instruction) in program.instructions.iter().enumerate() {
            let Some(shape) = check_shape(program, pc, instruction) else {
                continue;
            };
            let owner_index = owners.partition_point(|&(at, _)| at <= pc);
            let Some(&(start, owner)) = owner_index.checked_sub(1).and_then(|i| owners.get(i))
            else {
                continue;
            };
            ordinal = if previous_owner == Some(owner) {
                ordinal.saturating_add(1)
            } else {
                0
            };
            previous_owner = Some(owner);
            let (text, location) = program
                .instruction_spans
                .get(pc)
                .and_then(Option::as_ref)
                .and_then(|span| span_source(program, &sources, span))
                .map_or((String::new(), None), |(text, at)| (text, Some(at)));
            let path = |reg: Option<u8>| {
                reg.and_then(|reg| reference(program, &sources, start, pc, reg, 0))
            };
            sites.push(CheckSite {
                id: SiteId(u32::try_from(sites.len()).unwrap_or(u32::MAX)),
                pc,
                owner,
                ordinal,
                kind: shape.kind,
                operator: shape.operator,
                text,
                location,
                left_path: path(shape.left),
                right_path: path(shape.right),
            });
        }
        Self { rules, sites }
    }

    /// All checks, in program order (`sites()[i].id == SiteId(i)`).
    pub fn sites(&self) -> &[CheckSite] {
        &self.sites
    }

    /// The check with id `id`.
    pub fn site(&self, id: SiteId) -> Option<&CheckSite> {
        self.sites.get(usize::try_from(id.0).ok()?)
    }

    /// The check performed by the instruction at `pc`, if it is one.
    pub fn site_at(&self, pc: usize) -> Option<&CheckSite> {
        let index = self.sites.binary_search_by_key(&pc, |site| site.pc).ok()?;
        self.sites.get(index)
    }

    /// The rule or function with index `index`, as used by
    /// [`ConditionOwner::rule`].
    pub fn rule(&self, index: usize) -> Option<&RuleOwner> {
        self.rules.get(index)
    }
}

struct Shape {
    kind: ConditionKind,
    operator: Option<Operator>,
    left: Option<u8>,
    right: Option<u8>,
}

/// Classifies the instruction at `pc` if it checks a condition. The guards
/// the compiler adds to make sure a binding is defined are not checks.
fn check_shape(program: &Program, pc: usize, instruction: &Instruction) -> Option<Shape> {
    let shape = |kind, operator, left, right| Shape {
        kind,
        operator,
        left,
        right,
    };
    match *instruction {
        Instruction::Guard {
            register,
            mode: GuardMode::Condition,
        } => {
            let writer = pc
                .checked_sub(1)
                .and_then(|previous| program.instructions.get(previous));
            let comparison = |operator, left, right| {
                shape(
                    ConditionKind::Comparison,
                    Some(operator),
                    Some(left),
                    Some(right),
                )
            };
            Some(match writer.copied() {
                Some(Instruction::Eq { dest, left, right }) if dest == register => {
                    comparison(Operator::Eq, left, right)
                }
                Some(Instruction::Ne { dest, left, right }) if dest == register => {
                    comparison(Operator::Ne, left, right)
                }
                Some(Instruction::Lt { dest, left, right }) if dest == register => {
                    comparison(Operator::Lt, left, right)
                }
                Some(Instruction::Le { dest, left, right }) if dest == register => {
                    comparison(Operator::Le, left, right)
                }
                Some(Instruction::Gt { dest, left, right }) if dest == register => {
                    comparison(Operator::Gt, left, right)
                }
                Some(Instruction::Ge { dest, left, right }) if dest == register => {
                    comparison(Operator::Ge, left, right)
                }
                Some(Instruction::Contains {
                    dest,
                    collection,
                    value,
                }) if dest == register => shape(
                    ConditionKind::Membership,
                    Some(Operator::In),
                    Some(value),
                    Some(collection),
                ),
                Some(Instruction::Not { dest, operand }) if dest == register => {
                    shape(ConditionKind::Negation, None, Some(operand), None)
                }
                _ => shape(ConditionKind::Truthiness, None, Some(register), None),
            })
        }
        Instruction::Guard {
            register,
            mode: GuardMode::Not,
        } => Some(shape(ConditionKind::Negation, None, Some(register), None)),
        Instruction::AssertEq { left, right } => Some(shape(
            ConditionKind::Comparison,
            Some(Operator::Eq),
            Some(left),
            Some(right),
        )),
        Instruction::LoopStart { params_index } => {
            let params = program.instruction_data.get_loop_params(params_index)?;
            Some(shape(
                ConditionKind::Iteration,
                None,
                Some(params.collection),
                None,
            ))
        }
        _ => None,
    }
}

/// Start of each rule body and argument-matching block, sorted by pc. The
/// compiler emits each rule's code contiguously, so a body runs from its
/// start to the next start.
fn owner_starts(program: &Program) -> Vec<(usize, ConditionOwner)> {
    let mut starts = Vec::new();
    for (rule, info) in program.rule_infos.iter().enumerate() {
        for (definition, bodies) in info.definitions.iter().enumerate() {
            let destructuring = info.destructuring_blocks.get(definition).copied().flatten();
            let entries = destructuring.map(|pc| (pc, None)).into_iter().chain(
                bodies
                    .iter()
                    .enumerate()
                    .map(|(body, &pc)| (pc, Some(body))),
            );
            for (pc, body) in entries {
                if let Ok(pc) = usize::try_from(pc) {
                    let owner = ConditionOwner {
                        rule,
                        definition,
                        body,
                    };
                    starts.push((pc, owner));
                }
            }
        }
    }
    starts.sort_by_key(|&(pc, _)| pc);
    starts
}

/// The reference that register `reg` holds at `pc`, as written. Looks back
/// from `pc` to `start` for the instruction that wrote the register.
fn reference(
    program: &Program,
    sources: &[SourceIndex],
    start: usize,
    pc: usize,
    reg: u8,
    depth: u8,
) -> Option<String> {
    if depth > 16 {
        return None;
    }
    let data = &program.instruction_data;
    let at = (start..pc).rev().find(|&at| {
        program
            .instructions
            .get(at)
            .is_some_and(|i| writes(program, i, reg))
    })?;
    match *program.instructions.get(at)? {
        Instruction::Move { src, .. } => {
            reference(program, sources, start, at, src, depth.saturating_add(1))
        }
        Instruction::LoopStart { params_index } => {
            let params = data.get_loop_params(params_index)?;
            // A loop that needs no key, such as `every x in xs`, uses one
            // register for the key and the value; it holds the value.
            if params.value_reg != reg {
                return None;
            }
            let collection = reference(
                program,
                sources,
                start,
                at,
                params.collection,
                depth.saturating_add(1),
            )?;
            Some(alloc::format!("{collection}[_]"))
        }
        Instruction::LoadInput { .. }
        | Instruction::LoadData { .. }
        | Instruction::Index { .. }
        | Instruction::IndexLiteral { .. }
        | Instruction::ChainedIndex { .. }
        | Instruction::VirtualDataDocumentLookup { .. }
        | Instruction::CallRule { .. } => {
            let span = program.instruction_spans.get(at)?.as_ref()?;
            span_source(program, sources, span).map(|(text, _)| text)
        }
        _ => None,
    }
}

/// Whether `instruction` writes register `reg`. Loop and comprehension
/// registers are attributed to the instruction that starts the loop or
/// comprehension.
fn writes(program: &Program, instruction: &Instruction, reg: u8) -> bool {
    use Instruction::*;
    let data = &program.instruction_data;
    match *instruction {
        Load { dest, .. }
        | LoadTrue { dest }
        | LoadFalse { dest }
        | LoadNull { dest }
        | LoadBool { dest, .. }
        | LoadData { dest }
        | LoadInput { dest }
        | LoadContext { dest }
        | LoadMetadata { dest }
        | Move { dest, .. }
        | Add { dest, .. }
        | Sub { dest, .. }
        | Mul { dest, .. }
        | Div { dest, .. }
        | Mod { dest, .. }
        | Eq { dest, .. }
        | Ne { dest, .. }
        | Lt { dest, .. }
        | Le { dest, .. }
        | Gt { dest, .. }
        | Ge { dest, .. }
        | And { dest, .. }
        | Or { dest, .. }
        | Not { dest, .. }
        | HostAwait { dest, .. }
        | Index { dest, .. }
        | IndexLiteral { dest, .. }
        | ArrayNew { dest }
        | SetNew { dest }
        | Contains { dest, .. }
        | Count { dest, .. }
        | CallRule { dest, .. }
        | PolicyCondition { dest, .. } => dest == reg,
        ArrayPush { arr, .. } | ArrayPushDefined { arr, .. } => arr == reg,
        SetAdd { set, .. } => set == reg,
        ObjectSet { obj, .. } => obj == reg,
        CoalesceUndefinedToNull { register } => register == reg,
        RuleInit { result_reg, .. } => result_reg == reg,
        LogicalBlockStart { result, .. }
        | AllOfNext { result, .. }
        | AnyOfNext { result, .. }
        | LogicalBlockEnd { result, .. } => result == reg,
        BuiltinCall { params_index } => data
            .get_builtin_call_params(params_index)
            .is_some_and(|p| p.dest == reg),
        FunctionCall { params_index } => data
            .get_function_call_params(params_index)
            .is_some_and(|p| p.dest == reg),
        ObjectCreate { params_index } => data
            .get_object_create_params(params_index)
            .is_some_and(|p| p.dest == reg),
        ArrayCreate { params_index } => data
            .get_array_create_params(params_index)
            .is_some_and(|p| p.dest == reg),
        SetCreate { params_index } => data
            .get_set_create_params(params_index)
            .is_some_and(|p| p.dest == reg),
        VirtualDataDocumentLookup { params_index } => data
            .get_virtual_data_document_lookup_params(params_index)
            .is_some_and(|p| p.dest == reg),
        ChainedIndex { params_index } => data
            .get_chained_index_params(params_index)
            .is_some_and(|p| p.dest == reg),
        LoopStart { params_index } => data
            .get_loop_params(params_index)
            .is_some_and(|p| p.key_reg == reg || p.value_reg == reg || p.result_reg == reg),
        ComprehensionBegin { params_index } => data
            .get_comprehension_begin_params(params_index)
            .is_some_and(|p| p.key_reg == reg || p.value_reg == reg || p.result_reg == reg),
        Return { .. }
        | AssertEq { .. }
        | Guard { .. }
        | ReturnUndefinedIfNotTrue { .. }
        | LoopNext { .. }
        | DestructuringSuccess {}
        | RuleReturn {}
        | Halt {}
        | ComprehensionYield { .. }
        | ComprehensionEnd {} => false,
    }
}

fn span_source(
    program: &Program,
    sources: &[SourceIndex],
    span: &SpanInfo,
) -> Option<(String, SourceLocation)> {
    sources.get(span.source_index)?.text(program, span)
}

/// Maps the lexer's (line, column) positions in one source to byte offsets.
///
/// The lexer counts a tab as 4 columns and a character of a raw string as 1
/// column; everything else is counted in bytes. A string token's span
/// excludes its quotes, so a range that starts or ends inside the quotes is
/// widened to include them.
struct SourceIndex {
    /// Byte offset of the start of each line.
    lines: Vec<usize>,
    /// Byte offsets of the opening and closing quote of each string, and
    /// whether it is a raw string.
    strings: Vec<(usize, usize, bool)>,
}

impl SourceIndex {
    fn new(content: &str) -> Self {
        let mut lines = alloc::vec![0];
        let mut strings = Vec::new();
        let mut open: Option<(usize, char)> = None;
        let mut comment = false;
        let mut escaped = false;
        for (at, ch) in content.char_indices() {
            if ch == '\n' {
                lines.push(at.saturating_add(1));
                comment = false;
            }
            match open {
                _ if comment => {}
                Some((_, '"')) if escaped => escaped = false,
                Some((_, '"')) if ch == '\\' => escaped = true,
                Some((start, quote)) if ch == quote => {
                    strings.push((start, at, quote == '`'));
                    open = None;
                }
                Some(_) => {}
                None if ch == '"' || ch == '`' => open = Some((at, ch)),
                None if ch == '#' => comment = true,
                None => {}
            }
        }
        Self { lines, strings }
    }

    fn string_at(&self, at: usize) -> Option<(usize, usize, bool)> {
        let index = self.strings.partition_point(|&(open, _, _)| open < at);
        let (open, close, raw) = *self.strings.get(index.checked_sub(1)?)?;
        (at <= close).then_some((open, close, raw))
    }

    /// Text of `span` in `program` and where it starts.
    fn text(&self, program: &Program, span: &SpanInfo) -> Option<(String, SourceLocation)> {
        let source = program.sources.get(span.source_index)?;
        let content = source.content.as_str();
        let (start, end) = self.range(content, span)?;
        let text = content.get(start..end)?.to_string();
        let line = self.lines.partition_point(|&at| at <= start);
        let line_start = *self.lines.get(line.checked_sub(1)?)?;
        let location = SourceLocation {
            file: source.name.clone(),
            line,
            column: self.columns(content, line_start, start)?,
        };
        Some((text, location))
    }

    /// Lexer column of byte offset `at` on the line starting at `line_start`.
    fn columns(&self, content: &str, line_start: usize, at: usize) -> Option<usize> {
        self.positions(content, line_start)
            .find(|&(offset, _)| offset >= at)
            .filter(|&(offset, _)| offset == at)
            .map(|(_, column)| column)
    }

    /// Byte offset of the lexer position (`line`, `column`).
    fn offset(&self, content: &str, line: usize, column: usize) -> Option<usize> {
        let line_start = *self.lines.get(line.checked_sub(1)?)?;
        self.positions(content, line_start)
            .find(|&(_, at)| at >= column)
            .filter(|&(_, at)| at == column)
            .map(|(offset, _)| offset)
    }

    /// The byte offset and lexer column of each character of the line
    /// starting at `line_start`, and of the end of the line.
    fn positions<'a>(
        &'a self,
        content: &'a str,
        line_start: usize,
    ) -> impl Iterator<Item = (usize, usize)> + 'a {
        let line = content.get(line_start..).unwrap_or_default();
        let line = line.split_inclusive('\n').next().unwrap_or_default();
        let end = line_start.saturating_add(line.trim_end_matches('\n').len());
        line.char_indices()
            .map(move |(offset, ch)| (line_start.saturating_add(offset), ch))
            .chain(core::iter::once((end, '\n')))
            .scan(1_usize, move |column, (offset, ch)| {
                let here = *column;
                let raw = self
                    .string_at(offset)
                    .is_some_and(|(open, _, raw)| raw && open < offset);
                *column = column.saturating_add(match ch {
                    '\t' => 4,
                    '\r' if !raw => 0,
                    _ if raw => 1,
                    _ => ch.len_utf8(),
                });
                Some((offset, here))
            })
            .take_while(move |&(offset, _)| offset <= end)
    }

    /// Byte range of `span`, including the quotes of strings at its ends.
    ///
    /// The parser gives a reference such as `input.user.name`,
    /// `data.roles[input.role]` or `f(x)` the line and column of its last
    /// `.`, `[` or `(`, but the length of the whole reference. The end of
    /// the reference is found from that separator and the start from the
    /// length.
    fn range(&self, content: &str, span: &SpanInfo) -> Option<(usize, usize)> {
        let at = self.offset(content, span.line, span.column)?;
        let start = match content.get(at..)?.chars().next()? {
            '.' | '[' | '(' => self.reference_end(content, at)?.checked_sub(span.length)?,
            _ => at,
        };
        let end = start.checked_add(span.length)?;
        content.get(start..end)?;
        // A span that starts at a string's first character starts at its
        // opening quote; one that ends at a closing quote includes it.
        let opening = self
            .string_at(start)
            .filter(|&(open, _, _)| open.checked_add(1) == Some(start));
        let closing = self
            .string_at(end)
            .filter(|&(open, close, _)| close == end && open < end);
        Some((
            opening.map_or(start, |(open, _, _)| open),
            closing.map_or(end, |(_, close, _)| close.saturating_add(1)),
        ))
    }

    /// End of the reference whose last separator is at byte `at`: the end of
    /// the field after a `.`, or just past the bracket matching a `[` or `(`.
    fn reference_end(&self, content: &str, at: usize) -> Option<usize> {
        let rest = content.get(at..)?;
        if rest.starts_with('.') {
            let field = rest
                .get(1..)?
                .find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
                .unwrap_or(rest.len().saturating_sub(1));
            return at.checked_add(field)?.checked_add(1);
        }
        let mut depth = 0_usize;
        let mut chars = rest.char_indices();
        while let Some((offset, ch)) = chars.next() {
            let offset = at.saturating_add(offset);
            match ch {
                '"' | '`' => {
                    let (_, close, _) = self.string_at(offset.saturating_add(1))?;
                    while chars
                        .next()
                        .is_some_and(|(next, _)| at.saturating_add(next) < close)
                    {
                    }
                }
                '[' | '(' | '{' => depth = depth.saturating_add(1),
                ']' | ')' | '}' => {
                    depth = depth.checked_sub(1)?;
                    if depth == 0 {
                        return offset.checked_add(1);
                    }
                }
                '#' => {
                    let line_end = content.get(offset..)?.find('\n')?;
                    let line_end = offset.saturating_add(line_end);
                    while chars
                        .next()
                        .is_some_and(|(next, _)| at.saturating_add(next) < line_end)
                    {
                    }
                }
                _ => {}
            }
        }
        None
    }
}

#[cfg(test)]
#[allow(clippy::panic_in_result_fn)]
mod tests;
