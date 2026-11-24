// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Compiler-authored logical-negation boundaries, not runtime scope events.
//! Missing metadata requires source recompilation for scope capture. Hoisted
//! operands remain explicitly unavailable until their re-entry ownership is
//! defined. Neither condition prevents ordinary bytecode execution.

use crate::rvm::instructions::{GuardMode, Instruction};
use crate::rvm::program::Program;
use crate::Value;
use alloc::string::ToString as _;
use alloc::vec;
use alloc::vec::Vec;
use thiserror::Error;

pub const ANNOTATION: &str = "regorus.explain.negation";
const VERSION: u64 = 1;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NegationBoundary {
    Operand {
        entry_pc: usize,
        not_pc: usize,
        check_pc: usize,
    },
    HoistedOperand {
        not_pc: usize,
        check_pc: usize,
    },
}

impl NegationBoundary {
    pub(crate) const fn not_pc(&self) -> usize {
        match *self {
            Self::Operand { not_pc, .. } | Self::HoistedOperand { not_pc, .. } => not_pc,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NegationMetadata {
    Absent,
    Present(Vec<NegationBoundary>),
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum MetadataError {
    #[error("invalid logical-negation metadata shape or integer")]
    Shape,
    #[error("unsupported logical-negation metadata version")]
    Version,
    #[error("logical-negation metadata does not match the program")]
    Stale,
    #[error("logical-negation metadata PCs are out of bounds")]
    Bounds,
    #[error("logical-negation metadata sites are duplicated or unordered")]
    Ordering,
    #[error("logical-negation metadata omits a logical Not site")]
    Coverage,
    #[error("logical-negation metadata does not identify a real Not and its Guard")]
    Instruction,
    #[error("logical-negation metadata source spans are missing or inconsistent")]
    Span,
    #[error("cannot encode logical-negation program identity")]
    Identity,
}

// Detect accidental reuse after bytecode, parameters, owners or source changes.
// This is an integrity hint, not authentication of an untrusted program.
fn identity(program: &Program) -> Result<u64, MetadataError> {
    let bytes = postcard::to_allocvec(&(
        &program.instructions,
        &program.instruction_data,
        &program.instruction_spans,
        &program.sources,
        &program.rule_infos,
    ))
    .map_err(|_| MetadataError::Identity)?;
    let hash = bytes.iter().fold(0xcbf2_9ce4_8422_2325_u64, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3)
    });
    // The annotation serialization bridge stores signed integers.
    Ok(hash & 0x7fff_ffff_ffff_ffff)
}

pub fn encode(
    program: &Program,
    boundaries: &[NegationBoundary],
) -> Result<Value, MetadataError> {
    let rows: Vec<Value> = boundaries
        .iter()
        .map(|boundary| match *boundary {
            NegationBoundary::Operand {
                entry_pc,
                not_pc,
                check_pc,
            } => Value::from(vec![
                Value::from(0_u64),
                Value::from(entry_pc),
                Value::from(not_pc),
                Value::from(check_pc),
            ]),
            NegationBoundary::HoistedOperand { not_pc, check_pc } => Value::from(vec![
                Value::from(1_u64),
                Value::from(not_pc),
                Value::from(check_pc),
            ]),
        })
        .collect();
    Ok(Value::from(vec![
        Value::from(VERSION),
        Value::from(identity(program)?),
        Value::from(rows),
    ]))
}

fn integer(value: Option<&Value>) -> Result<usize, MetadataError> {
    usize::try_from(
        value
            .ok_or(MetadataError::Shape)?
            .as_u64()
            .map_err(|_| MetadataError::Shape)?,
    )
    .map_err(|_| MetadataError::Shape)
}

fn validate_site(program: &Program, not_pc: usize, check_pc: usize) -> Result<(), MetadataError> {
    if check_pc >= program.instructions.len() || not_pc >= program.instructions.len() {
        return Err(MetadataError::Bounds);
    }
    if not_pc.checked_add(1) != Some(check_pc) {
        return Err(MetadataError::Instruction);
    }
    match (
        program.instructions.get(not_pc).copied(),
        program.instructions.get(check_pc).copied(),
    ) {
        (
            Some(Instruction::Not { dest, operand }),
            Some(Instruction::Guard {
                register,
                mode: GuardMode::Condition,
            }),
        ) if dest == register && dest != operand => {}
        _ => return Err(MetadataError::Instruction),
    }
    let span = program
        .instruction_spans
        .get(not_pc)
        .and_then(Option::as_ref)
        .ok_or(MetadataError::Span)?;
    let check_span = program
        .instruction_spans
        .get(check_pc)
        .and_then(Option::as_ref)
        .ok_or(MetadataError::Span)?;
    if (span.source_index, span.line, span.column, span.length)
        != (
            check_span.source_index,
            check_span.line,
            check_span.column,
            check_span.length,
        )
    {
        return Err(MetadataError::Span);
    }
    let source = program
        .sources
        .get(span.source_index)
        .ok_or(MetadataError::Span)?;
    let line = span
        .line
        .checked_sub(1)
        .and_then(|line| source.content.lines().nth(line))
        .ok_or(MetadataError::Span)?;
    let column = span.column.checked_sub(1).ok_or(MetadataError::Span)?;
    let mut visual = 0_usize;
    let mut offset = None;
    for (index, byte) in line.bytes().enumerate() {
        if visual == column {
            offset = Some(index);
            break;
        }
        visual = visual
            .checked_add(if byte == b'\t' { 4 } else { 1 })
            .ok_or(MetadataError::Span)?;
    }
    let text = offset
        .and_then(|offset| line.get(offset..))
        .ok_or(MetadataError::Span)?;
    if !text.strip_prefix("not").is_some_and(|rest| {
        rest.chars()
            .next()
            .is_some_and(|ch| !ch.is_alphanumeric() && ch != '_')
    }) {
        return Err(MetadataError::Span);
    }
    Ok(())
}

pub fn decode(program: &Program) -> Result<NegationMetadata, MetadataError> {
    let Some(annotation) = program.metadata.annotations.get(ANNOTATION) else {
        return Ok(NegationMetadata::Absent);
    };
    let header = annotation.as_array().map_err(|_| MetadataError::Shape)?;
    if header.len() != 3 {
        return Err(MetadataError::Shape);
    }
    if integer(header.get(0))? != usize::try_from(VERSION).map_err(|_| MetadataError::Version)? {
        return Err(MetadataError::Version);
    }
    let saved_identity = header
        .get(1)
        .ok_or(MetadataError::Shape)?
        .as_u64()
        .map_err(|_| MetadataError::Shape)?;
    if saved_identity != identity(program)? {
        return Err(MetadataError::Stale);
    }
    let rows = header
        .get(2)
        .ok_or(MetadataError::Shape)?
        .as_array()
        .map_err(|_| MetadataError::Shape)?;
    if rows.len() > program.instructions.len() {
        return Err(MetadataError::Bounds);
    }
    let mut boundaries = Vec::new();
    let mut previous = None;
    for row in rows.iter() {
        let row = row.as_array().map_err(|_| MetadataError::Shape)?;
        let (boundary, not_pc, check_pc) = match (integer(row.get(0))?, row.len()) {
            (0, 4) => {
                let entry_pc = integer(row.get(1))?;
                let not_pc = integer(row.get(2))?;
                let check_pc = integer(row.get(3))?;
                if entry_pc > not_pc {
                    return Err(MetadataError::Bounds);
                }
                (
                    NegationBoundary::Operand {
                        entry_pc,
                        not_pc,
                        check_pc,
                    },
                    not_pc,
                    check_pc,
                )
            }
            (1, 3) => {
                let not_pc = integer(row.get(1))?;
                let check_pc = integer(row.get(2))?;
                (
                    NegationBoundary::HoistedOperand { not_pc, check_pc },
                    not_pc,
                    check_pc,
                )
            }
            _ => return Err(MetadataError::Shape),
        };
        if previous.is_some_and(|previous| previous >= not_pc) {
            return Err(MetadataError::Ordering);
        }
        validate_site(program, not_pc, check_pc)?;
        previous = Some(not_pc);
        boundaries.push(boundary);
    }
    for (pc, instruction) in program.instructions.iter().enumerate() {
        let Instruction::Not { dest, operand } = *instruction else {
            continue;
        };
        if dest == operand {
            continue;
        }
        let check_pc = pc.checked_add(1).ok_or(MetadataError::Bounds)?;
        if matches!(
            program.instructions.get(check_pc).copied(),
            Some(Instruction::Guard {
                register,
                mode: GuardMode::Condition,
            }) if register == dest
        ) {
            validate_site(program, pc, check_pc)?;
            if boundaries
                .binary_search_by_key(&pc, NegationBoundary::not_pc)
                .is_err()
            {
                return Err(MetadataError::Coverage);
            }
        }
    }
    Ok(NegationMetadata::Present(boundaries))
}

pub fn finish(
    program: &mut Program,
    mut boundaries: Vec<NegationBoundary>,
) -> Result<(), MetadataError> {
    boundaries.sort_unstable_by_key(NegationBoundary::not_pc);
    let metadata = encode(program, &boundaries)?;
    program
        .metadata
        .annotations
        .insert(ANNOTATION.to_string(), metadata);
    match decode(program)? {
        NegationMetadata::Present(decoded) if decoded == boundaries => Ok(()),
        _ => Err(MetadataError::Identity),
    }
}

#[cfg(test)]
mod tests;
