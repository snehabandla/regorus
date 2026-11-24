// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::panic_in_result_fn)]

use super::{
    decode, encode, identity, MetadataError, NegationBoundary, NegationMetadata, ANNOTATION, VERSION,
};
use crate::explain::{ConditionKind, Provenance};
use crate::languages::rego::compiler::Compiler;
use crate::rvm::program::{DeserializationResult, Program};
use crate::rvm::vm::{ExecutionMode, ExecutionState, RegoVM};
use crate::rvm::Instruction;
use crate::{Engine, Rc, Value};
use alloc::string::ToString as _;
use alloc::vec;
use alloc::vec::Vec;
use anyhow::{bail, Context as _, Result};

fn compile(policy: &str, host: &[(&str, usize)]) -> Result<Program> {
    let mut engine = Engine::new();
    engine.add_policy("negation.rego".to_string(), policy.to_string())?;
    let entry: Rc<str> = "data.t.allow".into();
    let policy = engine.compile_with_entrypoint(&entry)?;
    Ok(
        Compiler::compile_from_policy_with_host_await(&policy, &["data.t.allow"], host)?
            .as_ref()
            .clone(),
    )
}

fn boundaries(program: &Program) -> Result<Vec<NegationBoundary>> {
    match decode(program)? {
        NegationMetadata::Present(boundaries) => Ok(boundaries),
        NegationMetadata::Absent => bail!("compiler did not emit negation metadata"),
    }
}

fn execute(program: &Program, input: &str, mode: ExecutionMode) -> Result<Value> {
    let mut vm = RegoVM::new();
    vm.load_program(alloc::sync::Arc::new(program.clone()));
    vm.set_input(Value::from_json_str(input)?);
    vm.set_execution_mode(mode);
    let result = vm.execute()?;
    if mode == ExecutionMode::RunToCompletion {
        return Ok(result);
    }
    match vm.execution_state() {
        ExecutionState::Completed { result } => Ok(result.clone()),
        other => bail!("did not complete: {other:?}"),
    }
}

fn roundtrips(program: &Program) -> Result<[Program; 2]> {
    let json = Program::deserialize_json(&program.serialize_json().map_err(anyhow::Error::msg)?)
        .map_err(anyhow::Error::msg)?;
    let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
    assert_eq!(binary.get(4..8), Some(6_u32.to_le_bytes().as_slice()));
    let binary = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(program) => program,
        DeserializationResult::Partial(_) => bail!("version 6 unexpectedly requires recompilation"),
    };
    Ok([json, binary])
}

fn bytecode(program: &Program) -> Result<Vec<u8>> {
    postcard::to_allocvec(&(&program.instructions, &program.instruction_spans))
        .map_err(|error| anyhow::Error::msg(error.to_string()))
}

#[test]
fn operand_entry_precedes_calls_and_retains_guard_provenance() -> Result<()> {
    let program = compile(
        "package t\nhelper(x) := x\nallow if { not helper(input.blocked) }\n",
        &[],
    )?;
    let sites = boundaries(&program)?;
    let NegationBoundary::Operand {
        entry_pc,
        not_pc,
        check_pc,
    } = *sites.first().context("missing site")?
    else {
        bail!("ordinary call marked hoisted");
    };
    assert!(entry_pc < not_pc);
    assert!(program
        .instructions
        .get(entry_pc..not_pc)
        .context("operand")?
        .iter()
        .any(|instruction| matches!(instruction, Instruction::FunctionCall { .. })));
    let provenance = Provenance::new(&program);
    let site = provenance.site_at(check_pc).context("missing Guard site")?;
    assert_eq!(site.kind, ConditionKind::Negation);
    assert_eq!(site.text, "not helper(input.blocked)");
    assert!(site.location.is_some());
    let mut unannotated = program.clone();
    unannotated.metadata.annotations.remove(ANNOTATION);
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for (input, expected) in [
            ("{}", Value::Bool(true)),
            (r#"{"blocked":false}"#, Value::Bool(true)),
            (r#"{"blocked":true}"#, Value::Undefined),
        ] {
            assert_eq!(execute(&program, input, mode)?, expected);
            assert_eq!(execute(&unannotated, input, mode)?, expected);
        }
    }
    Ok(())
}

#[test]
fn bound_operand_enters_at_not_and_tabs_preserve_source_identity() -> Result<()> {
    let program = compile("package t\nallow if { x := false;\tnot(x) }\n", &[])?;
    let sites = boundaries(&program)?;
    assert!(matches!(
        sites.first(),
        Some(NegationBoundary::Operand { entry_pc, not_pc, .. }) if entry_pc == not_pc
    ));
    Ok(())
}

#[test]
fn synthetic_membership_and_host_routing_nots_are_not_boundaries() -> Result<()> {
    for (policy, host, expected) in [
        ("package t\nallow if { \"k\", 1 in input.m }\n", &[][..], 0),
        (
            "package t\nallow if { not \"k\", 1 in input.m }\n",
            &[][..],
            1,
        ),
        (
            "package t\nremote(x) := x\nallow if { not remote(input.x) }\n",
            &[("remote", 1)][..],
            1,
        ),
    ] {
        let program = compile(policy, host)?;
        let sites = boundaries(&program)?;
        assert_eq!(sites.len(), expected);
        let all_nots = program
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, Instruction::Not { .. }))
            .count();
        assert!(all_nots > sites.len());
    }
    Ok(())
}

#[test]
fn nested_comprehension_boundaries_are_nested_but_not_synthetic() -> Result<()> {
    let program = compile(
        "package t\nallow if { not [1 | not input.blocked] == [] }\n",
        &[],
    )?;
    let sites = boundaries(&program)?;
    assert_eq!(sites.len(), 2);
    let mut ranges = Vec::new();
    for site in sites {
        let NegationBoundary::Operand {
            entry_pc, not_pc, ..
        } = site
        else {
            bail!("comprehension-local operand unexpectedly hoisted");
        };
        ranges.push((entry_pc, not_pc));
    }
    let inner = ranges.first().context("inner")?;
    let outer = ranges.get(1).context("outer")?;
    assert!(outer.0 < inner.0 && inner.1 < outer.1);
    Ok(())
}

#[test]
fn upstream_hoisted_operands_never_claim_partial_entry() -> Result<()> {
    for policy in [
        "package t\nallow if { not input.xs[_] }\n",
        "package t\nhelper(x) := x\nallow if { not helper(input.xs[_]) }\n",
        "package t\ncollection := input.xs\nallow if { not collection[_] }\n",
    ] {
        let program = compile(policy, &[])?;
        let sites = boundaries(&program)?;
        assert_eq!(sites.len(), 1);
        assert!(matches!(
            sites.first(),
            Some(NegationBoundary::HoistedOperand { .. })
        ));
        let mut unannotated = program.clone();
        unannotated.metadata.annotations.remove(ANNOTATION);
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for input in [
                r#"{"xs":[]}"#,
                r#"{"xs":[false,false]}"#,
                r#"{"xs":[true,false]}"#,
            ] {
                assert_eq!(
                    execute(&program, input, mode)?,
                    execute(&unannotated, input, mode)?
                );
            }
        }
        for restored in roundtrips(&program)? {
            assert_eq!(boundaries(&restored)?, sites);
        }
    }
    Ok(())
}

#[test]
fn metadata_absence_empty_and_annotated_v6_roundtrip_without_bytecode_changes() -> Result<()> {
    for policy in [
        "package t\nallow := true\n",
        "package t\nallow if { not input.x }\n",
    ] {
        let program = compile(policy, &[])?;
        let expected = decode(&program)?;
        let original_bytecode = bytecode(&program)?;
        let mut old = program.clone();
        old.metadata.annotations.remove(ANNOTATION);
        assert_eq!(decode(&old)?, NegationMetadata::Absent);
        for artifact in [&program, &old] {
            for restored in roundtrips(artifact)? {
                assert_eq!(bytecode(&restored)?, original_bytecode);
                assert_eq!(decode(&restored)?, decode(artifact)?);
                for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                    assert_eq!(execute(&restored, "{}", mode)?, Value::Bool(true));
                }
            }
        }
        assert_eq!(decode(&program)?, expected);
    }
    assert_eq!(
        decode(&compile("package t\nallow := true\n", &[])?)?,
        NegationMetadata::Present(Vec::new())
    );
    Ok(())
}

#[test]
fn malformed_metadata_is_an_explicit_error_not_an_execution_failure() -> Result<()> {
    let program = compile("package t\nallow if { not input.x }\n", &[])?;
    for value in [
        Value::Null,
        Value::from(vec![]),
        Value::from(vec![
            Value::from(2_u64),
            Value::from(identity(&program)?),
            Value::from(vec![]),
        ]),
    ] {
        let mut malformed = program.clone();
        malformed
            .metadata
            .annotations
            .insert(ANNOTATION.to_string(), value);
        assert!(matches!(
            decode(&malformed),
            Err(MetadataError::Shape | MetadataError::Version)
        ));
        for restored in roundtrips(&malformed)? {
            assert!(decode(&restored).is_err());
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                assert_eq!(execute(&restored, "{}", mode)?, Value::Bool(true));
            }
        }
    }
    Ok(())
}

fn with_rows(program: &Program, rows: Vec<Value>) -> Result<Program> {
    let mut program = program.clone();
    let metadata = Value::from(vec![
        Value::from(VERSION),
        Value::from(identity(&program)?),
        Value::from(rows),
    ]);
    program
        .metadata
        .annotations
        .insert(ANNOTATION.to_string(), metadata);
    Ok(program)
}

#[test]
fn decoder_rejects_bounds_types_duplicates_ordering_and_wrong_instruction_pairs() -> Result<()> {
    let program = compile("package t\nallow if { not input.x; not input.y }\n", &[])?;
    let sites = boundaries(&program)?;
    let NegationBoundary::Operand {
        entry_pc,
        not_pc,
        check_pc,
    } = *sites.first().context("site")?
    else {
        bail!("hoisted");
    };
    let row = Value::from(vec![
        Value::from(0_u64),
        Value::from(entry_pc),
        Value::from(not_pc),
        Value::from(check_pc),
    ]);
    let rows = [
        (vec![row.clone(), row.clone()], MetadataError::Ordering),
        (
            vec![Value::from(vec![
                Value::from(0_u64),
                Value::Bool(false),
                Value::from(not_pc),
                Value::from(check_pc),
            ])],
            MetadataError::Shape,
        ),
        (
            vec![Value::from(vec![
                Value::from(1_u64),
                Value::from(not_pc),
                Value::from(program.instructions.len()),
            ])],
            MetadataError::Bounds,
        ),
        (
            vec![Value::from(vec![
                Value::from(1_u64),
                Value::from(check_pc),
                Value::from(check_pc.saturating_add(1)),
            ])],
            MetadataError::Instruction,
        ),
        (
            vec![Value::from(vec![
                Value::from(0_u64),
                Value::from(check_pc),
                Value::from(not_pc),
                Value::from(check_pc),
            ])],
            MetadataError::Bounds,
        ),
    ];
    for (rows, expected) in rows {
        assert_eq!(decode(&with_rows(&program, rows)?), Err(expected));
    }
    assert_eq!(
        decode(&with_rows(&program, Vec::new())?),
        Err(MetadataError::Coverage)
    );
    let mut reversed = sites;
    reversed.reverse();
    let mut altered = program.clone();
    altered
        .metadata
        .annotations
        .insert(ANNOTATION.to_string(), encode(&program, &reversed)?);
    assert_eq!(decode(&altered), Err(MetadataError::Ordering));
    Ok(())
}

#[test]
fn stale_program_identity_and_inconsistent_spans_are_explicit_errors() -> Result<()> {
    let program = compile("package t\nallow if { not input.x }\n", &[])?;
    let sites = boundaries(&program)?;
    let mut stale = program.clone();
    stale.instructions.push(Instruction::Halt {});
    assert_eq!(decode(&stale), Err(MetadataError::Stale));
    let mut stale_source = program.clone();
    stale_source
        .sources
        .first_mut()
        .context("source")?
        .content
        .push(' ');
    assert_eq!(decode(&stale_source), Err(MetadataError::Stale));
    let NegationBoundary::Operand { check_pc, .. } = *sites.first().context("site")?
    else {
        bail!("hoisted");
    };
    let mut inconsistent = program.clone();
    *inconsistent.instruction_spans.get_mut(check_pc).context("span")? = None;
    let metadata = encode(&inconsistent, &sites)?;
    inconsistent
        .metadata
        .annotations
        .insert(ANNOTATION.to_string(), metadata);
    assert_eq!(decode(&inconsistent), Err(MetadataError::Span));
    Ok(())
}
