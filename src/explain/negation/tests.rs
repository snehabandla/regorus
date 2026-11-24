// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::panic_in_result_fn)]

use super::{
    decode, encode, identity, MetadataError, NegationBoundary, NegationMetadata, ANNOTATION,
    VERSION,
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
    let compiled_policy = engine.compile_with_entrypoint(&entry)?;
    Ok(
        Compiler::compile_from_policy_with_host_await(&compiled_policy, &["data.t.allow"], host)?
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
    let returned = vm.execute()?;
    if mode == ExecutionMode::RunToCompletion {
        return Ok(returned);
    }
    match *vm.execution_state() {
        ExecutionState::Completed { ref result } => Ok(result.clone()),
        ref other => bail!("did not complete: {other:?}"),
    }
}

fn roundtrips(program: &Program) -> Result<[Program; 2]> {
    let json = Program::deserialize_json(&program.serialize_json().map_err(anyhow::Error::msg)?)
        .map_err(anyhow::Error::msg)?;
    let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
    assert_eq!(binary.get(4..8), Some(6_u32.to_le_bytes().as_slice()));
    let binary = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(restored) => restored,
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
            assert!(matches!(
                decode(&restored),
                Err(MetadataError::Shape | MetadataError::Version)
            ));
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
    let cases = [
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
    for (rows, expected) in cases {
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
    let NegationBoundary::Operand { check_pc, .. } = *sites.first().context("site")? else {
        bail!("hoisted");
    };
    let mut inconsistent = program.clone();
    *inconsistent
        .instruction_spans
        .get_mut(check_pc)
        .context("span")? = None;
    let metadata = encode(&inconsistent, &sites)?;
    inconsistent
        .metadata
        .annotations
        .insert(ANNOTATION.to_string(), metadata);
    assert_eq!(decode(&inconsistent), Err(MetadataError::Span));
    Ok(())
}

#[test]
fn raw_unicode_before_not_preserves_lexer_source_coordinates() -> Result<()> {
    let program = compile(
        "package t\nallow if { x := `é`; not input.blocked }\n",
        &[],
    )?;
    assert_eq!(boundaries(&program)?.len(), 1);
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        assert_eq!(execute(&program, "{}", mode)?, Value::Bool(true));
    }
    Ok(())
}

#[test]
fn multiline_not_preserves_a_valid_logical_boundary() -> Result<()> {
    let program = compile("package t\nallow if { not\n input.blocked }\n", &[])?;
    assert_eq!(boundaries(&program)?.len(), 1);
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        assert_eq!(execute(&program, "{}", mode)?, Value::Bool(true));
    }
    Ok(())
}

fn replace_annotation_number(
    program: &Program,
    path: &[usize],
    number: Value,
) -> Result<Program> {
    let mut altered = program.clone();
    let mut slot = altered
        .metadata
        .annotations
        .get_mut(ANNOTATION)
        .context("annotation")?;
    for index in path {
        slot = slot
            .as_array_mut()?
            .get_mut(*index)
            .context("annotation array slot")?;
    }
    *slot = number;
    Ok(altered)
}

#[test]
fn fractional_metadata_version_is_not_laundered_by_binary_serialization() -> Result<()> {
    let program = compile("package t\nallow if { not input.blocked }\n", &[])?;
    let altered = replace_annotation_number(&program, &[0], Value::from(1.5_f64))?;
    let [json, binary] = roundtrips(&altered)?;
    let dispositions = [
        ("direct", decode(&altered)),
        ("json", decode(&json)),
        ("binary", decode(&binary)),
    ];
    for (format, disposition) in &dispositions {
        std::println!("fractional_version format={format} disposition={disposition:?}");
    }
    for candidate in [&altered, &json, &binary] {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            assert_eq!(execute(candidate, "{}", mode)?, Value::Bool(true));
        }
    }
    for (format, disposition) in dispositions {
        assert_eq!(disposition, Err(MetadataError::Shape), "{format}");
    }
    Ok(())
}

#[test]
fn integral_float_annotation_slots_require_integer_representation() -> Result<()> {
    let program = compile("package t\nallow if { not input.blocked }\n", &[])?;
    let sites = boundaries(&program)?;
    let NegationBoundary::Operand {
        entry_pc,
        not_pc,
        check_pc,
    } = *sites.first().context("site")?
    else {
        bail!("hoisted");
    };
    let cases = [
        ("version", vec![0], Value::from(1.0_f64)),
        ("identity", vec![1], Value::from(0.0_f64)),
        ("tag", vec![2, 0, 0], Value::from(0.0_f64)),
        (
            "entry",
            vec![2, 0, 1],
            Value::from(f64::from(u32::try_from(entry_pc)?)),
        ),
        (
            "not",
            vec![2, 0, 2],
            Value::from(f64::from(u32::try_from(not_pc)?)),
        ),
        (
            "guard",
            vec![2, 0, 3],
            Value::from(f64::from(u32::try_from(check_pc)?)),
        ),
    ];
    let mut direct_dispositions = Vec::new();
    for (name, path, number) in cases {
        let altered = replace_annotation_number(&program, &path, number)?;
        let [json, binary] = roundtrips(&altered)?;
        let disposition = decode(&altered);
        std::println!(
            "integral_float slot={name} direct={disposition:?} json={:?} binary={:?}",
            decode(&json),
            decode(&binary),
        );
        for candidate in [&altered, &json, &binary] {
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                assert_eq!(execute(candidate, "{}", mode)?, Value::Bool(true));
            }
        }
        direct_dispositions.push((name, disposition));
    }
    // JSON/metadata serialization may canonicalize integral floats to integer
    // representations. The logs expose that separately from direct decoding.
    for (name, disposition) in direct_dispositions {
        assert_eq!(disposition, Err(MetadataError::Shape), "{name}");
    }
    Ok(())
}

#[test]
#[ignore = "quantitative source-prefix control; run explicitly with --nocapture"]
fn negation_growing_source_prefix_measurements() -> Result<()> {
    for (rules, prefix_lines) in [(64_usize, 80_usize), (500, 640)] {
        let mut engine = Engine::new();
        let mut source = alloc::format!("{}\n", "#".repeat(768)).repeat(prefix_lines);
        source.push_str("package t.checks\n");
        let prefix_bytes = source.len();
        for rule in 0..rules {
            source.push_str(&alloc::format!("r{rule} if {{ "));
            source.push_str(&"not input.blocked; ".repeat(16));
            source.push_str("}\n");
        }
        let source_bytes = source.len();
        engine.add_policy("checks.rego".to_string(), source)?;
        engine.add_policy(
            "entry.rego".to_string(),
            "package t\nallow := data.t.checks\n".to_string(),
        )?;
        let entry: Rc<str> = "data.t.allow".into();
        let started = std::time::Instant::now();
        let compiled_policy = engine.compile_with_entrypoint(&entry)?;
        let program = Compiler::compile_from_policy(&compiled_policy, &["data.t.allow"])?;
        let compile_elapsed = started.elapsed();
        let started = std::time::Instant::now();
        let sites = boundaries(&program)?;
        let decode_elapsed = started.elapsed();
        let expected_sites = rules.checked_mul(16).context("site count overflow")?;
        assert_eq!(sites.len(), expected_sites);
        let prefix_scan_lower_bound = prefix_bytes
            .checked_mul(expected_sites)
            .and_then(|bytes| bytes.checked_mul(2))
            .context("scan count overflow")?;
        std::println!(
            "negation_prefix sites={} source_bytes={source_bytes} prefix_bytes={prefix_bytes} \
             two_pass_prefix_scan_lower_bound={prefix_scan_lower_bound} \
             compile={compile_elapsed:?} decode={decode_elapsed:?}",
            sites.len(),
        );
    }
    Ok(())
}

#[test]
fn negation_external_artifact_capture_disposition() -> Result<()> {
    let Some(prefix) = std::env::var_os("B29C_DECODE_PREFIX") else {
        return Ok(());
    };
    let prefix = std::path::PathBuf::from(prefix);
    anyhow::ensure!(
        !prefix.as_os_str().is_empty()
            && prefix
                .components()
                .all(|component| matches!(component, std::path::Component::Normal(_))),
        "artifact prefix must be relative and contained in the working directory"
    );
    let expected = std::env::var("B29C_EXPECT_METADATA").context("expected capture disposition")?;
    let json = Program::deserialize_json(&std::fs::read_to_string(prefix.with_extension("json"))?)
        .map_err(anyhow::Error::msg)?;
    let binary_bytes = std::fs::read(prefix.with_extension("bin"))?;
    let binary = match Program::deserialize_binary(&binary_bytes).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(restored) => restored,
        DeserializationResult::Partial(_) => bail!("external version-6 artifact is partial"),
    };
    let json_metadata = decode(&json)?;
    let binary_metadata = decode(&binary)?;
    assert_eq!(json_metadata, binary_metadata);
    match (expected.as_str(), json_metadata) {
        ("absent", NegationMetadata::Absent) => {}
        ("present", NegationMetadata::Present(sites)) => assert_eq!(sites.len(), 1),
        (requested, actual) => bail!("expected {requested}, decoded {actual:?}"),
    }
    for candidate in [&json, &binary] {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            assert_eq!(execute(candidate, "{}", mode)?, Value::Bool(true));
        }
    }
    Ok(())
}
