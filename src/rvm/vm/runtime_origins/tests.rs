// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use anyhow::{Context as _, Result};

use crate::explain::ExplanationRecorder;
use crate::languages::rego::compiler::Compiler;
use crate::rvm::instructions::{Instruction, LiteralOrRegister};
use crate::rvm::program::Program;
use crate::{Engine, Rc};

use super::super::execution_model::{ExecutionMode, ExecutionState};
use super::{ConcretePath, PathRoot, PathSegment, RegoVM, RuntimeOrigin, Value};

struct Recorder;
impl ExplanationRecorder for Recorder {}

fn v(json: &str) -> Result<Value> {
    Value::from_json_str(json)
}

fn source(epoch: u64, segments: Vec<PathSegment>) -> RuntimeOrigin {
    RuntimeOrigin::Source {
        epoch,
        path: ConcretePath::Captured {
            root: PathRoot::Input,
            segments,
        },
    }
}

fn instruction(vm: &mut RegoVM, program: &Program, instruction: Instruction) -> Result<()> {
    vm.execute_instruction(program, instruction)?;
    Ok(())
}

fn compile(policy: &str) -> Result<Arc<Program>> {
    let mut engine = Engine::new();
    engine.add_policy("origins.rego".into(), policy.into())?;
    let compiled = engine.compile_with_entrypoint(&Rc::from("data.t.r"))?;
    Ok(Compiler::compile_from_policy(&compiled, &["data.t.r"])?)
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn source_identity_is_typed_and_moves_preserve_it_without_value_matching() -> Result<()> {
    let mut program = Program::new();
    program.dispatch_window_size = 8;
    program.literals = vec![v(r#""a""#)?, v(r#""b""#)?, v(r#""0""#)?, v("0")?];
    let mut vm = RegoVM::new();
    vm.load_program(Arc::new(program.clone()));
    vm.set_input(v(r#"{"a":[],"b":[],"0":[9]}"#)?);
    vm.set_explanation_recorder(Box::new(Recorder));
    instruction(&mut vm, &program, Instruction::LoadInput { dest: 0 })?;
    let epoch = vm.explain.origins.epoch;
    for (dest, literal_idx) in [(1, 0), (2, 1), (3, 2)] {
        instruction(
            &mut vm,
            &program,
            Instruction::IndexLiteral {
                dest,
                container: 0,
                literal_idx,
            },
        )?;
    }
    assert_eq!(vm.get_register(1)?, vm.get_register(2)?);
    let a = vm.explain.origins.get(1);
    assert_eq!(a, source(epoch, vec![PathSegment::Key("a".into())]));
    assert_ne!(a, vm.explain.origins.get(2));
    instruction(&mut vm, &program, Instruction::Move { dest: 4, src: 1 })?;
    instruction(&mut vm, &program, Instruction::Move { dest: 4, src: 4 })?;
    assert_eq!(a, vm.explain.origins.get(4));
    instruction(
        &mut vm,
        &program,
        Instruction::Load {
            dest: 5,
            literal_idx: 3,
        },
    )?;
    instruction(
        &mut vm,
        &program,
        Instruction::Index {
            dest: 3,
            container: 3,
            key: 5,
        },
    )?;
    assert_eq!(
        vm.explain.origins.get(3),
        source(
            epoch,
            vec![PathSegment::Key("0".into()), PathSegment::Index(0),]
        )
    );
    instruction(
        &mut vm,
        &program,
        Instruction::Index {
            dest: 6,
            container: 0,
            key: 5,
        },
    )?;
    assert_eq!(vm.explain.origins.get(6), RuntimeOrigin::Unknown);
    let equal_value = vm.get_register(1)?.clone();
    vm.set_register(4, equal_value)?;
    assert_eq!(vm.explain.origins.get(4), RuntimeOrigin::Unknown);
    vm.take_register(1)?;
    assert_eq!(vm.explain.origins.get(1), RuntimeOrigin::Unknown);
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn computed_instances_are_fresh_and_members_are_not_claimed_as_source_values() -> Result<()> {
    let mut program = Program::new();
    program.dispatch_window_size = 4;
    program.literals = vec![v("[1]")?, v("0")?];
    let mut vm = RegoVM::new();
    vm.load_program(Arc::new(program.clone()));
    vm.set_explanation_recorder(Box::new(Recorder));
    instruction(
        &mut vm,
        &program,
        Instruction::Load {
            dest: 0,
            literal_idx: 0,
        },
    )?;
    let first = vm.explain.origins.get(0);
    instruction(
        &mut vm,
        &program,
        Instruction::Load {
            dest: 1,
            literal_idx: 0,
        },
    )?;
    assert_eq!(vm.get_register(0)?, vm.get_register(1)?);
    assert!(matches!(first, RuntimeOrigin::Computed { .. }));
    assert_ne!(first, vm.explain.origins.get(1));
    instruction(&mut vm, &program, Instruction::Move { dest: 2, src: 0 })?;
    assert_eq!(first, vm.explain.origins.get(2));
    instruction(
        &mut vm,
        &program,
        Instruction::IndexLiteral {
            dest: 2,
            container: 2,
            literal_idx: 1,
        },
    )?;
    assert_eq!(vm.get_register(2)?, &v("1")?);
    assert_eq!(vm.explain.origins.get(2), RuntimeOrigin::Unknown);
    instruction(
        &mut vm,
        &program,
        Instruction::Load {
            dest: 0,
            literal_idx: 0,
        },
    )?;
    assert_ne!(first, vm.explain.origins.get(0));
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn chained_paths_preserve_punctuation_and_unrepresentable_members_stay_unknown() -> Result<()> {
    let mut program = Program::new();
    program.dispatch_window_size = 4;
    program.literals = vec![v(r#""a.[\"0\"]""#)?, v("0")?, v(r#""x""#)?];
    let params = crate::rvm::instructions::ChainedIndexParams {
        dest: 1,
        root: 0,
        path_components: vec![
            LiteralOrRegister::Literal(0),
            LiteralOrRegister::Literal(1),
            LiteralOrRegister::Literal(2),
        ],
    };
    let params_index = program.instruction_data.add_chained_index_params(params);
    let mut vm = RegoVM::new();
    vm.load_program(Arc::new(program.clone()));
    vm.set_input(v(r#"{"a.[\"0\"]":[{"x":7}]}"#)?);
    vm.set_explanation_recorder(Box::new(Recorder));
    instruction(&mut vm, &program, Instruction::LoadInput { dest: 0 })?;
    instruction(
        &mut vm,
        &program,
        Instruction::ChainedIndex { params_index },
    )?;
    assert_eq!(vm.get_register(1)?, &v("7")?);
    assert_eq!(
        vm.explain.origins.get(1),
        source(
            vm.explain.origins.epoch,
            vec![
                PathSegment::Key("a.[\"0\"]".into()),
                PathSegment::Index(0),
                PathSegment::Key("x".into()),
            ]
        )
    );
    let root = vm.explain.origins.source(PathRoot::Input);
    let mut object = Value::new_object();
    object.as_object_mut()?.insert(v("0")?, v("[]")?);
    assert_eq!(root.indexed(&object, &v("0")?), RuntimeOrigin::Unknown);
    let set = Value::from(alloc::collections::BTreeSet::from([v("1")?]));
    assert_eq!(root.indexed(&set, &v("1")?), RuntimeOrigin::Unknown);
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn native_invocation_restores_the_callers_origin_window() -> Result<()> {
    let program = compile("package t\ninner := input.inside\nr := inner\n")?;
    let rule_index = program
        .rule_infos
        .iter()
        .position(|info| info.name == "data.t.inner")
        .context("compiled inner rule exists")?;
    let info = program
        .rule_infos
        .get(rule_index)
        .context("inner rule metadata")?;
    assert!(!info.definitions.is_empty());
    assert!(info.result_reg < info.num_registers);
    let input = v(r#"{"inside":[1],"outside":[2]}"#)?;
    let mut baseline = None;
    for recording in [false, true] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_input(input.clone());
        assert!(vm.registers.len() >= 2);
        if recording {
            vm.set_explanation_recorder(Box::new(Recorder));
        }
        instruction(&mut vm, &program, Instruction::LoadInput { dest: 0 })?;
        let outer = vm.explain.origins.get(0);
        // RuleInit requires the context installed by normal call dispatch.
        instruction(
            &mut vm,
            &program,
            Instruction::CallRule {
                dest: 1,
                rule_index: u16::try_from(rule_index)?,
            },
        )?;
        let result = vm.get_register(1)?.clone();
        assert_eq!(result, v("[1]")?);
        assert_eq!(vm.get_register(0)?, &input);
        assert!(vm.call_rule_stack.is_empty());
        assert!(vm.register_stack.is_empty());
        assert!(vm.explain.origins.windows.is_empty());
        if recording {
            assert_eq!(Some(result), baseline);
            assert_eq!(outer, source(vm.explain.origins.epoch, Vec::new()));
            assert_eq!(outer, vm.explain.origins.get(0));
            assert_eq!(vm.explain.origins.get(1), RuntimeOrigin::Unknown);
        } else {
            baseline = Some(result);
            assert!(vm.explain.origins.registers.is_empty());
        }
    }
    Ok(())
}

fn contains_key(origins: &[RuntimeOrigin], key: &str) -> bool {
    origins.iter().any(|origin| {
        matches!(origin,
            RuntimeOrigin::Source { path: ConcretePath::Captured { segments, .. }, .. }
                if segments == &[PathSegment::Key(key.into())]
        )
    })
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn suspension_preserves_nested_windows_and_reset_partitions_evaluations() -> Result<()> {
    let program = compile(
        "package t\ninner := [input.inside, __builtin_host_await(input.flag,\"inner\")]\n\
         r := [input.outside, inner, __builtin_host_await(input.flag,\"outer\")]\n",
    )?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_input(v(r#"{"inside":[1],"outside":[2],"flag":true}"#)?);
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.set_explanation_recorder(Box::new(Recorder));
    vm.execute()?;
    let first_epoch = vm.explain.origins.epoch;
    assert_eq!(vm.get_host_await_identifier(), Some(&v(r#""inner""#)?));
    assert!(contains_key(&vm.explain.origins.registers, "inside"));
    assert!(vm
        .explain
        .origins
        .windows
        .iter()
        .any(|window| contains_key(window, "outside")));
    vm.resume(Some(Value::Bool(true)))?;
    assert_eq!(vm.explain.origins.epoch, first_epoch);
    assert_eq!(vm.get_host_await_identifier(), Some(&v(r#""outer""#)?));
    assert!(contains_key(&vm.explain.origins.registers, "outside"));
    assert!(!contains_key(&vm.explain.origins.registers, "inside"));
    vm.resume(Some(Value::Bool(false)))?;
    assert!(
        matches!(vm.execution_state(), ExecutionState::Completed { result }
        if result == &v("[[2],[[1],true],false]")?)
    );
    assert!(vm.explain.origins.windows.is_empty());
    vm.execute()?;
    assert_ne!(vm.explain.origins.epoch, first_epoch);
    vm.set_max_instructions(1);
    assert!(matches!(
        vm.resume(Some(Value::Bool(true))),
        Err(crate::rvm::vm::VmError::InstructionLimitExceeded { .. })
    ));
    assert!(vm.explain.origins.registers.is_empty());
    assert!(vm.explain.origins.windows.is_empty());
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn replacing_a_recorder_while_suspended_does_not_recover_old_origins_by_equality() -> Result<()> {
    let program = compile(
        "package t\ninner := [input.inside, __builtin_host_await(input.flag,\"inner\")]\n\
         r := [input.outside, inner, __builtin_host_await(input.flag,\"outer\")]\n",
    )?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_input(v(r#"{"inside":[1],"outside":[1],"flag":true}"#)?);
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.set_explanation_recorder(Box::new(Recorder));
    vm.execute()?;
    let recorder = vm
        .take_explanation_recorder()
        .context("installed recorder")?;
    vm.set_explanation_recorder(recorder);
    assert!(vm.explain.origins.registers.is_empty());
    assert!(vm.explain.origins.windows.is_empty());
    vm.resume(Some(Value::Bool(true)))?;
    assert_eq!(vm.get_host_await_identifier(), Some(&v(r#""outer""#)?));
    assert!(!contains_key(&vm.explain.origins.registers, "outside"));
    vm.resume(Some(Value::Bool(false)))?;
    assert!(
        matches!(vm.execution_state(), ExecutionState::Completed { result }
        if result == &v("[[1],[[1],true],false]")?)
    );
    assert!(vm.explain.origins.windows.is_empty());
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn recorder_off_has_no_origin_storage_and_preserves_outcomes_in_both_modes() -> Result<()> {
    let program = compile("package t\nr := [input.a, input.b]\n")?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_input(v(r#"{"a":[1],"b":[1]}"#)?);
        vm.set_execution_mode(mode);
        vm.execute()?;
        let off = vm.execution_state().clone();
        assert!(vm.explain.origins.registers.is_empty());
        assert!(vm.explain.origins.windows.is_empty());
        vm.set_explanation_recorder(Box::new(Recorder));
        vm.execute()?;
        assert_eq!(vm.execution_state(), &off);
        let recorder = vm
            .take_explanation_recorder()
            .context("installed recorder")?;
        assert!(vm.explain.origins.registers.is_empty());
        vm.execute()?;
        assert_eq!(vm.execution_state(), &off);
        vm.set_explanation_recorder(recorder);
        vm.execute()?;
        assert_eq!(vm.execution_state(), &off);
    }
    Ok(())
}

#[test]
#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
#[allow(clippy::panic_in_result_fn)]
fn overflowing_array_index_never_claims_a_nonexistent_source_slot() -> Result<()> {
    let mut program = Program::new();
    program.dispatch_window_size = 3;
    program.literals = vec![v("0")?, v("4294967296")?];
    let mut baseline = None;
    for recording in [false, true] {
        let mut vm = RegoVM::new();
        vm.load_program(Arc::new(program.clone()));
        vm.set_input(v("[[]]")?);
        if recording {
            vm.set_explanation_recorder(Box::new(Recorder));
        }
        instruction(&mut vm, &program, Instruction::LoadInput { dest: 0 })?;
        for (dest, literal_idx) in [(1, 0), (2, 1)] {
            instruction(
                &mut vm,
                &program,
                Instruction::IndexLiteral {
                    dest,
                    container: 0,
                    literal_idx,
                },
            )?;
        }
        assert_eq!(vm.get_register(1)?, &v("[]")?);
        let overflow_value = vm.get_register(2)?.clone();
        #[cfg(target_pointer_width = "32")]
        assert_eq!(overflow_value, v("[]")?);
        #[cfg(target_pointer_width = "64")]
        assert_eq!(overflow_value, Value::Undefined);
        if recording {
            assert_eq!(Some(overflow_value), baseline);
            let zero_origin = source(vm.explain.origins.epoch, vec![PathSegment::Index(0)]);
            assert_eq!(vm.explain.origins.get(1), zero_origin);
            let overflow_origin = vm.explain.origins.get(2);
            assert_eq!(overflow_origin, RuntimeOrigin::Unknown);
        } else {
            baseline = Some(overflow_value);
            assert!(vm.explain.origins.registers.is_empty());
        }
    }
    Ok(())
}

#[test]
#[cfg(feature = "std")]
#[allow(clippy::panic_in_result_fn)]
fn bounded_large_chained_index_observes_deadlines_with_and_without_origins() -> Result<()> {
    use core::num::NonZeroU32;
    use core::time::Duration;
    use std::time::Instant;

    use crate::rvm::vm::VmError;
    use crate::utils::limits::{acquire_limits_test_lock, ExecutionTimerConfig};

    let _guard = acquire_limits_test_lock();
    const DEPTH: usize = 4096;
    let mut input = v("7")?;
    for _ in 0..DEPTH {
        input = Value::from_array(vec![input]);
    }
    let mut program = Program::new();
    program.dispatch_window_size = 2;
    program.literals = vec![v("0")?];
    let params_index = program.instruction_data.add_chained_index_params(
        crate::rvm::instructions::ChainedIndexParams {
            dest: 1,
            root: 0,
            path_components: vec![LiteralOrRegister::Literal(0); DEPTH],
        },
    );
    program.instructions = vec![
        Instruction::LoadInput { dest: 0 },
        Instruction::ChainedIndex { params_index },
        Instruction::Return { value: 1 },
    ];
    program.instruction_spans = vec![None; program.instructions.len()];
    let program = Arc::new(program);
    let mut missed = Vec::new();
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for recording in [false, true] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_input(input.clone());
            vm.set_execution_mode(mode);
            if recording {
                vm.set_explanation_recorder(Box::new(Recorder));
            }
            for limit in [Duration::from_secs(60), Duration::ZERO] {
                vm.set_execution_timer_config(Some(ExecutionTimerConfig {
                    limit,
                    // Three opcodes cannot reach this interval by dispatch
                    // alone; recording must account for its added work.
                    check_interval: NonZeroU32::new(8).context("positive timer interval")?,
                }));
                let started = Instant::now();
                let outcome = vm.execute();
                let elapsed = started.elapsed();
                if limit.is_zero() && recording {
                    if !matches!(outcome, Err(VmError::TimeLimitExceeded { pc: 1, .. })) {
                        missed.push((mode, recording, elapsed, outcome));
                    } else {
                        assert!(matches!(
                            vm.execution_state(),
                            ExecutionState::Error {
                                error: VmError::TimeLimitExceeded { pc: 1, .. },
                            }
                        ));
                        assert!(vm.registers.is_empty());
                        assert!(vm.explain.origins.registers.is_empty());
                        assert!(vm.explain.origins.windows.is_empty());
                    }
                } else {
                    // The unrecorded zero-limit outcome is an established
                    // baseline gap, not changed by origin-only instrumentation.
                    assert_eq!(outcome, Ok(v("7")?));
                    assert!(
                        matches!(vm.execution_state(), ExecutionState::Completed { result }
                        if result == &v("7")?)
                    );
                    if recording {
                        assert_eq!(
                            vm.explain.origins.get(1),
                            source(vm.explain.origins.epoch, vec![PathSegment::Index(0); DEPTH],),
                        );
                    } else {
                        assert!(vm.explain.origins.registers.is_empty());
                        assert!(vm.explain.origins.windows.is_empty());
                    }
                }
            }
        }
    }
    assert!(
        missed.is_empty(),
        "deep traversal missed its deadline (mode, origins, elapsed, typed outcome): {missed:?}"
    );
    Ok(())
}
