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

#[cfg(feature = "std")]
fn run_member_depth_child(case: &str) -> Result<()> {
    use crate::rvm::instructions::ArrayCreateParams;
    let parts: Vec<_> = case.split(':').collect();
    let &[mode, recording, shared, cleanup] = parts.as_slice() else {
        anyhow::bail!("invalid member-depth scenario");
    };
    let mode = match mode {
        "native" => ExecutionMode::RunToCompletion,
        "suspendable" => ExecutionMode::Suspendable,
        _ => anyhow::bail!("invalid member-depth mode"),
    };
    let recording = recording == "on";
    let shared = shared == "shared";
    let mut program = Program::new();
    program.dispatch_window_size = 3;
    let wrapping = program
        .instruction_data
        .add_array_create_params(ArrayCreateParams {
            dest: 0,
            elements: vec![0],
        });
    program.instructions.push(Instruction::LoadTrue { dest: 0 });
    program.instructions.extend(core::iter::repeat_n(
        Instruction::ArrayCreate {
            params_index: wrapping,
        },
        5_000,
    ));
    // Main-frame return overwrites register zero in suspendable mode. Keep
    // the nested value alive so recorder teardown, not return, releases it.
    program
        .instructions
        .push(Instruction::Move { dest: 1, src: 0 });
    if shared {
        program
            .instructions
            .push(Instruction::Move { dest: 2, src: 1 });
    }
    program.instructions.extend([
        Instruction::LoadTrue { dest: 0 },
        Instruction::Return { value: 0 },
    ]);
    program.instruction_spans = vec![None; program.instructions.len()];
    let mut vm = RegoVM::new();
    vm.load_program(Arc::new(program));
    vm.set_execution_mode(mode);
    if recording {
        vm.set_explanation_recorder(Box::new(Recorder));
    }
    anyhow::ensure!(
        matches!(vm.execute()?, Value::Bool(true)),
        "boolean result required"
    );
    let snapshot = shared.then(|| vm.explain.origins.get(1));
    match cleanup {
        "remove" => {
            anyhow::ensure!(vm.take_explanation_recorder().is_some() == recording);
        }
        "replace" => vm.set_explanation_recorder(Box::new(Recorder)),
        "reset" => vm.set_input(Value::Null),
        "drop" => drop(vm),
        _ => anyhow::bail!("invalid member-depth cleanup"),
    }
    drop(snapshot);
    Ok(())
}

#[test]
#[cfg(feature = "std")]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
#[allow(clippy::panic_in_result_fn)]
fn deep_constructed_member_teardown_is_stack_bounded() -> Result<()> {
    use core::time::Duration;
    use std::process::{Command, Stdio};
    use std::time::Instant;
    const CHILD: &str = "REGORUS_MEMBER_DEPTH_CHILD";
    const NAME: &str =
        "rvm::vm::runtime_origins::tests::deep_constructed_member_teardown_is_stack_bounded";
    if let Ok(case) = std::env::var(CHILD) {
        return std::thread::Builder::new()
            .name("member-depth".into())
            .stack_size(512 * 1024)
            .spawn(move || run_member_depth_child(&case))?
            .join()
            .map_err(|_| anyhow::anyhow!("member-depth worker panicked"))?;
    }
    let mut failed = Vec::new();
    for mode in ["native", "suspendable"] {
        for recording in ["off", "on"] {
            for shared in ["single", "shared"] {
                for cleanup in ["remove", "replace", "reset", "drop"] {
                    let case = alloc::format!("{mode}:{recording}:{shared}:{cleanup}");
                    let mut child = Command::new(std::env::current_exe()?)
                        .args(["--exact", NAME, "--nocapture"])
                        .env(CHILD, &case)
                        .stdout(Stdio::inherit())
                        .stderr(Stdio::inherit())
                        .spawn()?;
                    let deadline = Instant::now() + Duration::from_secs(30);
                    loop {
                        if let Some(status) = child.try_wait()? {
                            if !status.success() {
                                failed.push(alloc::format!("{case}: {status}"));
                            }
                            break;
                        }
                        if Instant::now() >= deadline {
                            child.kill()?;
                            child.wait()?;
                            failed.push(alloc::format!("{case}: deadline exceeded"));
                            break;
                        }
                        std::thread::sleep(Duration::from_millis(10));
                    }
                }
            }
        }
    }
    anyhow::ensure!(
        failed.is_empty(),
        "member-depth subprocess failures: {failed:?}"
    );
    Ok(())
}

fn run_member_program(
    mut program: Program,
    input: Value,
    mode: ExecutionMode,
    recording: bool,
) -> Result<RegoVM> {
    program.dispatch_window_size = 16;
    program.instructions.extend([
        Instruction::LoadTrue { dest: 15 },
        Instruction::Return { value: 15 },
    ]);
    program.instruction_spans = vec![None; program.instructions.len()];
    let mut vm = RegoVM::new();
    vm.load_program(Arc::new(program));
    vm.set_input(input);
    vm.set_execution_mode(mode);
    if recording {
        vm.set_explanation_recorder(Box::new(Recorder));
    }
    anyhow::ensure!(vm.execute()? == Value::Bool(true));
    Ok(vm)
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn constructed_members_keep_nested_alias_snapshots_in_both_modes() -> Result<()> {
    use crate::rvm::instructions::{ArrayCreateParams, ChainedIndexParams, ObjectCreateParams};
    let mut program = Program::new();
    program.literals = vec![
        v(r#""a""#)?,
        v(r#""b""#)?,
        v("0")?,
        v("1")?,
        v(r#""k.[\"0\"]""#)?,
        v("{}")?,
        v(r#""x""#)?,
    ];
    let pair = program
        .instruction_data
        .add_array_create_params(ArrayCreateParams {
            dest: 1,
            elements: vec![1, 2],
        });
    let nested = program
        .instruction_data
        .add_array_create_params(ArrayCreateParams {
            dest: 4,
            elements: vec![1],
        });
    let undefined_array = program
        .instruction_data
        .add_array_create_params(ArrayCreateParams {
            dest: 12,
            elements: vec![14],
        });
    let object = program
        .instruction_data
        .add_object_create_params(ObjectCreateParams {
            dest: 5,
            template_literal_idx: 5,
            literal_key_fields: vec![(4, 2)],
            fields: vec![(10, 4)],
        });
    let undefined_object = program
        .instruction_data
        .add_object_create_params(ObjectCreateParams {
            dest: 13,
            template_literal_idx: 5,
            literal_key_fields: vec![(4, 14)],
            fields: vec![],
        });
    let projection = program
        .instruction_data
        .add_chained_index_params(ChainedIndexParams {
            dest: 6,
            root: 5,
            path_components: vec![
                LiteralOrRegister::Literal(4),
                LiteralOrRegister::Literal(2),
                LiteralOrRegister::Literal(3),
                LiteralOrRegister::Literal(2),
                LiteralOrRegister::Literal(6),
            ],
        });
    program.instructions = vec![
        Instruction::LoadInput { dest: 0 },
        Instruction::IndexLiteral {
            dest: 1,
            container: 0,
            literal_idx: 0,
        },
        Instruction::IndexLiteral {
            dest: 2,
            container: 0,
            literal_idx: 1,
        },
        Instruction::ArrayCreate { params_index: pair },
        Instruction::Move { dest: 3, src: 1 },
        Instruction::ArrayPush { arr: 1, value: 2 },
        Instruction::ArrayCreate {
            params_index: nested,
        },
        Instruction::Load {
            dest: 10,
            literal_idx: 4,
        },
        Instruction::ObjectCreate {
            params_index: object,
        },
        Instruction::ArrayPush { arr: 1, value: 1 },
        Instruction::ChainedIndex {
            params_index: projection,
        },
        Instruction::IndexLiteral {
            dest: 7,
            container: 3,
            literal_idx: 2,
        },
        Instruction::IndexLiteral {
            dest: 8,
            container: 3,
            literal_idx: 3,
        },
        Instruction::ArrayPushDefined { arr: 1, value: 14 },
        Instruction::ArrayCreate {
            params_index: undefined_array,
        },
        Instruction::ObjectCreate {
            params_index: undefined_object,
        },
    ];
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut baseline = None;
        let mut reuse_baseline = None;
        for recording in [false, true] {
            let mut vm = run_member_program(
                program.clone(),
                v(r#"{"a":[{"x":7}],"b":[{"x":7}]}"#)?,
                mode,
                recording,
            )?;
            assert_eq!(vm.get_register(1)?.as_array()?.len(), 4);
            assert_eq!(vm.get_register(3)?.as_array()?.len(), 2);
            assert_eq!(vm.get_register(6)?, &v("7")?);
            assert_eq!(vm.get_register(7)?, vm.get_register(8)?);
            assert_eq!(vm.get_register(12)?, &Value::Undefined);
            assert_eq!(vm.get_register(13)?, &Value::Undefined);
            let epoch = vm.explain.origins.epoch;
            if recording {
                assert_eq!(Some(vm.registers.clone()), baseline);
                assert_eq!(
                    vm.explain.origins.get(6),
                    source(
                        epoch,
                        vec![
                            PathSegment::Key("b".into()),
                            PathSegment::Index(0),
                            PathSegment::Key("x".into()),
                        ]
                    )
                );
                assert_eq!(
                    vm.explain.origins.get(7),
                    source(epoch, vec![PathSegment::Key("a".into())])
                );
                assert_eq!(
                    vm.explain.origins.get(8),
                    source(epoch, vec![PathSegment::Key("b".into())])
                );
                assert_ne!(vm.explain.origins.get(1), vm.explain.origins.get(3));
                assert_eq!(vm.explain.origins.get(12), RuntimeOrigin::Unknown);
                assert_eq!(vm.explain.origins.get(13), RuntimeOrigin::Unknown);
                let snapshot = vm.explain.origins.get(1);
                vm.explain.origins.enter_window(&[]);
                assert!(vm.explain.origins.registers.is_empty());
                vm.explain.origins.leave_window();
                assert_eq!(vm.explain.origins.get(1), snapshot);
                vm.explain.origins.resize(2, 16);
                assert_eq!(vm.explain.origins.get(1), snapshot);
                assert_eq!(vm.explain.origins.get(3), RuntimeOrigin::Unknown);
            } else {
                baseline = Some(vm.registers.clone());
                assert!(vm.explain.origins.registers.is_empty());
            }
            vm.set_input(v(r#"{"a":[{"x":9}],"b":[{"x":11}]}"#)?);
            assert!(vm.explain.origins.registers.is_empty());
            assert!(vm.explain.origins.windows.is_empty());
            assert_eq!(vm.execute()?, Value::Bool(true));
            assert_eq!(vm.get_register(6)?, &v("11")?);
            if recording {
                assert_eq!(Some(vm.registers.clone()), reuse_baseline);
                assert_ne!(vm.explain.origins.epoch, epoch);
                assert_eq!(
                    vm.explain.origins.get(6),
                    source(
                        vm.explain.origins.epoch,
                        vec![
                            PathSegment::Key("b".into()),
                            PathSegment::Index(0),
                            PathSegment::Key("x".into()),
                        ]
                    )
                );
            } else {
                reuse_baseline = Some(vm.registers.clone());
                assert!(vm.explain.origins.registers.is_empty());
            }
        }
    }
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn set_duplicate_correspondence_is_ambiguous_only_for_distinct_sources() -> Result<()> {
    use crate::rvm::instructions::SetCreateParams;
    let mut program = Program::new();
    program.literals = vec![v(r#""a""#)?, v(r#""b""#)?];
    let same = program
        .instruction_data
        .add_set_create_params(SetCreateParams {
            dest: 3,
            elements: vec![1, 1],
        });
    let different = program
        .instruction_data
        .add_set_create_params(SetCreateParams {
            dest: 5,
            elements: vec![1, 2],
        });
    program.instructions = vec![
        Instruction::LoadInput { dest: 0 },
        Instruction::IndexLiteral {
            dest: 1,
            container: 0,
            literal_idx: 0,
        },
        Instruction::IndexLiteral {
            dest: 2,
            container: 0,
            literal_idx: 1,
        },
        Instruction::SetCreate { params_index: same },
        Instruction::Move { dest: 4, src: 3 },
        Instruction::SetAdd { set: 3, value: 2 },
        Instruction::SetAdd { set: 3, value: 1 },
        Instruction::SetCreate {
            params_index: different,
        },
        Instruction::Index {
            dest: 6,
            container: 4,
            key: 1,
        },
        Instruction::Index {
            dest: 7,
            container: 3,
            key: 1,
        },
        Instruction::Index {
            dest: 8,
            container: 5,
            key: 1,
        },
        Instruction::SetNew { dest: 9 },
        Instruction::SetAdd { set: 9, value: 1 },
        Instruction::SetAdd { set: 9, value: 14 },
        Instruction::Index {
            dest: 10,
            container: 9,
            key: 1,
        },
    ];
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut baseline = None;
        for recording in [false, true] {
            let vm =
                run_member_program(program.clone(), v(r#"{"a":[1],"b":[1]}"#)?, mode, recording)?;
            assert_eq!(vm.get_register(6)?, &v("[1]")?);
            assert_eq!(vm.get_register(6)?, vm.get_register(7)?);
            assert_eq!(vm.get_register(6)?, vm.get_register(8)?);
            if recording {
                assert_eq!(Some(vm.registers.clone()), baseline);
                let a = source(vm.explain.origins.epoch, vec![PathSegment::Key("a".into())]);
                assert_eq!(vm.explain.origins.get(6), a);
                assert_eq!(vm.explain.origins.get(10), a);
                assert_eq!(vm.explain.origins.get(7), RuntimeOrigin::Unknown);
                assert_eq!(vm.explain.origins.get(8), RuntimeOrigin::Unknown);
            } else {
                baseline = Some(vm.registers.clone());
                assert!(vm.explain.origins.registers.is_empty());
            }
        }
    }
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn object_mutation_preserves_untouched_sources_and_prewrite_self_aliases() -> Result<()> {
    use crate::rvm::instructions::ChainedIndexParams;
    let mut program = Program::new();
    program.literals = vec![
        v(r#""left""#)?,
        v(r#""replacement""#)?,
        v(r#""change""#)?,
        v(r#""keep""#)?,
        v(r#""self""#)?,
    ];
    let nested = program
        .instruction_data
        .add_chained_index_params(ChainedIndexParams {
            dest: 8,
            root: 1,
            path_components: vec![LiteralOrRegister::Literal(4), LiteralOrRegister::Literal(3)],
        });
    program.instructions = vec![
        Instruction::LoadInput { dest: 0 },
        Instruction::IndexLiteral {
            dest: 1,
            container: 0,
            literal_idx: 0,
        },
        Instruction::Move { dest: 2, src: 1 },
        Instruction::IndexLiteral {
            dest: 3,
            container: 0,
            literal_idx: 1,
        },
        Instruction::Load {
            dest: 7,
            literal_idx: 2,
        },
        Instruction::ObjectSet {
            obj: 1,
            key: 7,
            value: 3,
        },
        Instruction::IndexLiteral {
            dest: 4,
            container: 1,
            literal_idx: 3,
        },
        Instruction::IndexLiteral {
            dest: 5,
            container: 1,
            literal_idx: 2,
        },
        Instruction::IndexLiteral {
            dest: 6,
            container: 2,
            literal_idx: 2,
        },
        Instruction::Load {
            dest: 7,
            literal_idx: 4,
        },
        Instruction::ObjectSet {
            obj: 1,
            key: 7,
            value: 1,
        },
        Instruction::ChainedIndex {
            params_index: nested,
        },
    ];
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut baseline = None;
        for recording in [false, true] {
            let vm = run_member_program(
                program.clone(),
                v(r#"{"left":{"keep":[1],"change":[1]},"replacement":[1]}"#)?,
                mode,
                recording,
            )?;
            assert_eq!(vm.get_register(4)?, &v("[1]")?);
            assert_eq!(vm.get_register(4)?, vm.get_register(5)?);
            assert_eq!(vm.get_register(4)?, vm.get_register(6)?);
            if recording {
                assert_eq!(Some(vm.registers.clone()), baseline);
                let epoch = vm.explain.origins.epoch;
                let keep = source(
                    epoch,
                    vec![
                        PathSegment::Key("left".into()),
                        PathSegment::Key("keep".into()),
                    ],
                );
                assert_eq!(vm.explain.origins.get(4), keep);
                assert_eq!(vm.explain.origins.get(8), keep);
                assert_eq!(
                    vm.explain.origins.get(5),
                    source(epoch, vec![PathSegment::Key("replacement".into())])
                );
                assert_eq!(
                    vm.explain.origins.get(6),
                    source(
                        epoch,
                        vec![
                            PathSegment::Key("left".into()),
                            PathSegment::Key("change".into()),
                        ]
                    )
                );
            } else {
                baseline = Some(vm.registers.clone());
                assert!(vm.explain.origins.registers.is_empty());
            }
        }
    }
    Ok(())
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
            assert_eq!(
                vm.explain.origins.get(1),
                source(
                    vm.explain.origins.epoch,
                    vec![PathSegment::Key("inside".into())]
                )
            );
        } else {
            baseline = Some(result);
            assert!(vm.explain.origins.registers.is_empty());
        }
    }
    Ok(())
}

fn g2_rule(program: &Program, name: &str) -> Result<u16> {
    let index = program
        .rule_infos
        .iter()
        .position(|info| info.name == name)
        .with_context(|| alloc::format!("compiled rule {name}"))?;
    Ok(u16::try_from(index)?)
}

fn g2_literal(program: &mut Program, json: &str) -> Result<u16> {
    let index = u16::try_from(program.literals.len())?;
    program.literals.push(v(json)?);
    Ok(index)
}

fn g2_call(program: &mut Program, name: &str, dest: u8, arg: u8) -> Result<Instruction> {
    let func_rule_index = g2_rule(program, name)?;
    anyhow::ensure!(
        program
            .rule_infos
            .get(usize::from(func_rule_index))
            .context("fixture function")?
            .function_info
            .is_some(),
        "fixture must dispatch an actual function"
    );
    let params_index =
        program.add_function_call_params(crate::rvm::instructions::FunctionCallParams {
            dest,
            func_rule_index,
            num_args: 1,
            args: [arg, 0, 0, 0, 0, 0, 0, 0],
        });
    Ok(Instruction::FunctionCall { params_index })
}

fn g2_driver(mut program: Program, instructions: Vec<Instruction>) -> Arc<Program> {
    // Append a root driver without relocating compiled rule/destructuring blocks.
    let entry = program.instructions.len();
    program.instructions.extend(instructions);
    program.instructions.extend([
        Instruction::LoadTrue { dest: 15 },
        Instruction::Return { value: 15 },
    ]);
    program
        .instruction_spans
        .resize(program.instructions.len(), None);
    program.dispatch_window_size = 16;
    program.entry_points.clear();
    program.entry_points.insert("g2-driver".into(), entry);
    Arc::new(program)
}

fn g2_vm(program: Arc<Program>, input: Value, mode: ExecutionMode, recording: bool) -> RegoVM {
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_input(input);
    vm.set_execution_mode(mode);
    if recording {
        vm.set_explanation_recorder(Box::new(Recorder));
    }
    vm
}

fn g2_execute(vm: &mut RegoVM) -> Result<()> {
    anyhow::ensure!(vm.execute_entry_point_by_index(0)? == Value::Bool(true));
    anyhow::ensure!(vm.call_rule_stack.is_empty());
    anyhow::ensure!(vm.register_stack.is_empty());
    anyhow::ensure!(vm.explain.origins.windows.is_empty());
    if !vm.explain_enabled() {
        anyhow::ensure!(vm.explain.origins.registers.is_empty());
    }
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn g2_helper_arguments_returns_and_nested_members() -> Result<()> {
    let mut program =
        (*compile("package t\nid(x) := x\nwrap(x) := [id(x)]\nr := wrap([input.a,input.b])\n")?)
            .clone();
    let a = g2_literal(&mut program, r#""a""#)?;
    let b = g2_literal(&mut program, r#""b""#)?;
    let zero = g2_literal(&mut program, "0")?;
    let one = g2_literal(&mut program, "1")?;
    let pair = program.instruction_data.add_array_create_params(
        crate::rvm::instructions::ArrayCreateParams {
            dest: 3,
            elements: vec![1, 2],
        },
    );
    let wrap = g2_call(&mut program, "data.t.wrap", 3, 3)?;
    let program = g2_driver(
        program,
        vec![
            Instruction::LoadInput { dest: 0 },
            Instruction::Move { dest: 10, src: 0 },
            Instruction::IndexLiteral {
                dest: 1,
                container: 0,
                literal_idx: a,
            },
            Instruction::IndexLiteral {
                dest: 2,
                container: 0,
                literal_idx: b,
            },
            Instruction::ArrayCreate { params_index: pair },
            wrap,
            Instruction::IndexLiteral {
                dest: 4,
                container: 3,
                literal_idx: zero,
            },
            Instruction::IndexLiteral {
                dest: 5,
                container: 4,
                literal_idx: zero,
            },
            Instruction::IndexLiteral {
                dest: 6,
                container: 4,
                literal_idx: one,
            },
        ],
    );
    let input = v(r#"{"a":[1],"b":[1]}"#)?;
    for recording in [false, true] {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = g2_vm(program.clone(), input.clone(), mode, recording);
            g2_execute(&mut vm)?;
            assert_eq!(vm.get_register(10)?, &input);
            assert_eq!(vm.get_register(3)?, &v("[[[1],[1]]]")?);
            assert_eq!(vm.get_register(5)?, &v("[1]")?);
            assert_eq!(vm.get_register(6)?, &v("[1]")?);
            if recording {
                let epoch = vm.explain.origins.epoch;
                assert_eq!(vm.explain.origins.get(10), source(epoch, vec![]));
                assert_eq!(
                    vm.explain.origins.get(5),
                    source(epoch, vec![PathSegment::Key("a".into())])
                );
                assert_eq!(
                    vm.explain.origins.get(6),
                    source(epoch, vec![PathSegment::Key("b".into())])
                );
            }
        }
    }
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn g2_boolean_identity_and_cached_default_boundaries() -> Result<()> {
    let mut program = (*compile(
        "package t\nid(x) := x\ncomputed(x) := x == true\n\
         default p := [false]\np := input.a if input.choose\n\
         default q := [false]\ndefault scalar := false\n\
         r := [id(input.flag),computed(input.flag),p,q,scalar]\n",
    )?)
    .clone();
    let flag = g2_literal(&mut program, r#""flag""#)?;
    let zero = g2_literal(&mut program, "0")?;
    let id = g2_call(&mut program, "data.t.id", 2, 1)?;
    let computed = g2_call(&mut program, "data.t.computed", 3, 1)?;
    let p = g2_rule(&program, "data.t.p")?;
    let q = g2_rule(&program, "data.t.q")?;
    let scalar = g2_rule(&program, "data.t.scalar")?;
    let program = g2_driver(
        program,
        vec![
            Instruction::LoadInput { dest: 0 },
            Instruction::IndexLiteral {
                dest: 1,
                container: 0,
                literal_idx: flag,
            },
            id,
            computed,
            Instruction::CallRule {
                dest: 6,
                rule_index: p,
            },
            Instruction::CallRule {
                dest: 7,
                rule_index: p,
            },
            Instruction::CallRule {
                dest: 8,
                rule_index: q,
            },
            Instruction::CallRule {
                dest: 9,
                rule_index: q,
            },
            Instruction::CallRule {
                dest: 10,
                rule_index: scalar,
            },
            Instruction::CallRule {
                dest: 11,
                rule_index: scalar,
            },
            Instruction::IndexLiteral {
                dest: 4,
                container: 6,
                literal_idx: zero,
            },
            Instruction::IndexLiteral {
                dest: 5,
                container: 8,
                literal_idx: zero,
            },
        ],
    );
    for recording in [false, true] {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for choose in [false, true] {
                let input = v(if choose {
                    r#"{"flag":false,"a":[false],"choose":true}"#
                } else {
                    r#"{"flag":false,"a":[false],"choose":false}"#
                })?;
                let mut vm = g2_vm(program.clone(), input, mode, recording);
                g2_execute(&mut vm)?;
                for reg in [2, 3, 4, 5, 10, 11] {
                    assert_eq!(vm.get_register(reg)?, &Value::Bool(false));
                }
                for reg in [6, 7, 8, 9] {
                    assert_eq!(vm.get_register(reg)?, &v("[false]")?);
                }
                if recording {
                    let epoch = vm.explain.origins.epoch;
                    assert_eq!(
                        vm.explain.origins.get(2),
                        source(epoch, vec![PathSegment::Key("flag".into())])
                    );
                    assert_eq!(vm.explain.origins.get(3), RuntimeOrigin::Unknown);
                    if choose {
                        assert_eq!(
                            vm.explain.origins.get(6),
                            source(epoch, vec![PathSegment::Key("a".into())])
                        );
                        assert_eq!(
                            vm.explain.origins.get(4),
                            source(
                                epoch,
                                vec![PathSegment::Key("a".into()), PathSegment::Index(0)]
                            )
                        );
                    } else {
                        assert!(matches!(
                            vm.explain.origins.get(6),
                            RuntimeOrigin::Computed { .. }
                        ));
                        assert_eq!(vm.explain.origins.get(4), RuntimeOrigin::Unknown);
                    }
                    assert_eq!(vm.explain.origins.get(6), vm.explain.origins.get(7));
                    assert!(matches!(
                        vm.explain.origins.get(8),
                        RuntimeOrigin::Computed { .. }
                    ));
                    assert_eq!(vm.explain.origins.get(8), vm.explain.origins.get(9));
                    assert_eq!(vm.explain.origins.get(5), RuntimeOrigin::Unknown);
                    assert_eq!(vm.explain.origins.get(10), RuntimeOrigin::Unknown);
                    assert_eq!(vm.explain.origins.get(11), RuntimeOrigin::Unknown);
                }
            }
        }
    }
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn g2_cache_keeps_first_selected_value_not_last_equal_definition() -> Result<()> {
    let program = (*compile("package t\np := input.a\np := input.b\nr := [p,p]\n")?).clone();
    let p = g2_rule(&program, "data.t.p")?;
    let info = program
        .rule_infos
        .get(usize::from(p))
        .context("fixture rule")?;
    assert_eq!(info.definitions.len(), 2);
    assert!(!info.early_exit_on_first_success);
    let program = g2_driver(
        program,
        vec![
            Instruction::LoadInput { dest: 0 },
            Instruction::Move { dest: 1, src: 0 },
            Instruction::CallRule {
                dest: 1,
                rule_index: p,
            },
            Instruction::CallRule {
                dest: 2,
                rule_index: p,
            },
        ],
    );
    let mut partial =
        (*compile("package t\ns contains input.a\ns contains input.b\nr := [s,s]\n")?).clone();
    let s = g2_rule(&partial, "data.t.s")?;
    assert_eq!(
        partial
            .rule_infos
            .get(usize::from(s))
            .context("fixture partial rule")?
            .definitions
            .len(),
        2
    );
    let a = g2_literal(&mut partial, "[1]")?;
    let b = g2_literal(&mut partial, "[2]")?;
    let partial = g2_driver(
        partial,
        vec![
            Instruction::LoadInput { dest: 0 },
            Instruction::CallRule {
                dest: 3,
                rule_index: s,
            },
            Instruction::CallRule {
                dest: 4,
                rule_index: s,
            },
            Instruction::IndexLiteral {
                dest: 5,
                container: 3,
                literal_idx: a,
            },
            Instruction::IndexLiteral {
                dest: 6,
                container: 3,
                literal_idx: b,
            },
            Instruction::IndexLiteral {
                dest: 7,
                container: 4,
                literal_idx: a,
            },
            Instruction::IndexLiteral {
                dest: 8,
                container: 4,
                literal_idx: b,
            },
        ],
    );
    for recording in [false, true] {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for conflict in [false, true] {
                let input = v(if conflict {
                    r#"{"a":[1],"b":[2]}"#
                } else {
                    r#"{"a":[1],"b":[1]}"#
                })?;
                let mut vm = g2_vm(program.clone(), input, mode, recording);
                g2_execute(&mut vm)?;
                let expected = if conflict {
                    Value::Undefined
                } else {
                    v("[1]")?
                };
                assert_eq!(vm.get_register(1)?, &expected);
                assert_eq!(vm.get_register(2)?, &expected);
                let cached = vm
                    .rule_cache
                    .get(usize::from(p))
                    .context("fixture cached rule")?;
                assert!(cached.0);
                assert_eq!(cached.1, expected);
                if recording {
                    let expected_origin = if conflict {
                        RuntimeOrigin::Unknown
                    } else {
                        source(vm.explain.origins.epoch, vec![PathSegment::Key("a".into())])
                    };
                    assert_eq!(vm.explain.origins.get(1), expected_origin);
                    assert_eq!(vm.explain.origins.get(2), expected_origin);
                }
            }
            let mut vm = g2_vm(partial.clone(), v(r#"{"a":[1],"b":[2]}"#)?, mode, recording);
            g2_execute(&mut vm)?;
            let expected = Value::from(alloc::collections::BTreeSet::from([v("[1]")?, v("[2]")?]));
            assert_eq!(vm.get_register(3)?, &expected);
            assert_eq!(vm.get_register(4)?, &expected);
            for (registers, value, key) in [([5, 7], v("[1]")?, "a"), ([6, 8], v("[2]")?, "b")] {
                for register in registers {
                    assert_eq!(vm.get_register(register)?, &value);
                    if recording {
                        assert_eq!(
                            vm.explain.origins.get(register),
                            source(vm.explain.origins.epoch, vec![PathSegment::Key(key.into())])
                        );
                    }
                }
            }
            if recording {
                assert!(matches!(
                    vm.explain.origins.get(3),
                    RuntimeOrigin::Collection { .. }
                ));
                assert_eq!(vm.explain.origins.get(3), vm.explain.origins.get(4));
            }
        }
    }
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn g2_missing_rejected_and_else_returns_replace_destination_origins() -> Result<()> {
    let mut program = (*compile(
        "package t\nproject(x) := x.missing\nmatched({\"k\": x}) := x\n\
         choose(x) := input.b if { false } else := x\n\
         r := [project(input.a),matched(input.a),choose(input.a)]\n",
    )?)
    .clone();
    let a = g2_literal(&mut program, r#""a""#)?;
    let absent = g2_literal(&mut program, r#""absent""#)?;
    let project = g2_call(&mut program, "data.t.project", 2, 1)?;
    let matched = g2_call(&mut program, "data.t.matched", 3, 1)?;
    let undefined_arg = g2_call(&mut program, "data.t.project", 5, 4)?;
    let choose = g2_call(&mut program, "data.t.choose", 1, 1)?;
    let program = g2_driver(
        program,
        vec![
            Instruction::LoadInput { dest: 0 },
            Instruction::IndexLiteral {
                dest: 1,
                container: 0,
                literal_idx: a,
            },
            Instruction::Move { dest: 2, src: 0 },
            Instruction::Move { dest: 3, src: 0 },
            project,
            matched,
            Instruction::IndexLiteral {
                dest: 4,
                container: 0,
                literal_idx: absent,
            },
            Instruction::Move { dest: 5, src: 0 },
            undefined_arg,
            choose,
        ],
    );
    for recording in [false, true] {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for matching in [false, true] {
                let input = v(if matching {
                    r#"{"a":{"k":[1]},"b":{"k":[1]}}"#
                } else {
                    r#"{"a":{},"b":{}}"#
                })?;
                let mut vm = g2_vm(program.clone(), input.clone(), mode, recording);
                g2_execute(&mut vm)?;
                assert_eq!(vm.get_register(1)?, &input[&v(r#""a""#)?]);
                assert_eq!(vm.get_register(2)?, &Value::Undefined);
                assert_eq!(vm.get_register(5)?, &Value::Undefined);
                assert_eq!(
                    vm.get_register(3)?,
                    &if matching {
                        v("[1]")?
                    } else {
                        Value::Undefined
                    }
                );
                if recording {
                    let epoch = vm.explain.origins.epoch;
                    assert_eq!(vm.explain.origins.get(2), RuntimeOrigin::Unknown);
                    assert_eq!(vm.explain.origins.get(5), RuntimeOrigin::Unknown);
                    assert_eq!(
                        vm.explain.origins.get(1),
                        source(epoch, vec![PathSegment::Key("a".into())])
                    );
                    assert_eq!(
                        vm.explain.origins.get(3),
                        if matching {
                            source(
                                epoch,
                                vec![PathSegment::Key("a".into()), PathSegment::Key("k".into())],
                            )
                        } else {
                            RuntimeOrigin::Unknown
                        }
                    );
                }
            }
        }
    }
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn g2_explicit_return_tracks_each_modes_actual_value_selection() -> Result<()> {
    for recording in [false, true] {
        for undefined_return in [false, true] {
            let mut program = (*compile("package t\np := input.a\nr := p\n")?).clone();
            let p = g2_rule(&program, "data.t.p")?;
            let a = g2_literal(&mut program, r#""a""#)?;
            let b = g2_literal(&mut program, r#""b""#)?;
            let entry = u32::try_from(program.instructions.len())?;
            program.instructions.extend([
                Instruction::RuleInit {
                    result_reg: 0,
                    rule_index: p,
                },
                Instruction::LoadInput { dest: 1 },
                Instruction::IndexLiteral {
                    dest: 0,
                    container: 1,
                    literal_idx: a,
                },
                Instruction::IndexLiteral {
                    dest: 2,
                    container: 1,
                    literal_idx: b,
                },
            ]);
            if undefined_return {
                program.instructions.extend([
                    Instruction::LoadFalse { dest: 2 },
                    Instruction::ReturnUndefinedIfNotTrue { condition: 2 },
                ]);
            } else {
                program.instructions.push(Instruction::Return { value: 2 });
            }
            let info = program
                .rule_infos
                .get_mut(usize::from(p))
                .context("fixture rule")?;
            info.result_reg = 0;
            info.num_registers = 3;
            info.definitions = Rc::new(vec![vec![entry]]);
            info.destructuring_blocks = vec![None];
            info.else_bodies = vec![vec![false]];
            program.max_rule_window_size = program.max_rule_window_size.max(3);
            let program = g2_driver(
                program,
                vec![
                    Instruction::LoadInput { dest: 0 },
                    Instruction::CallRule {
                        dest: 1,
                        rule_index: p,
                    },
                    Instruction::CallRule {
                        dest: 2,
                        rule_index: p,
                    },
                ],
            );
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = g2_vm(program.clone(), v(r#"{"a":[1],"b":[2]}"#)?, mode, recording);
                g2_execute(&mut vm)?;
                // Native selects result_reg even for an explicit return; do not repair parity here.
                let (expected_value, key) = match (mode, undefined_return) {
                    (ExecutionMode::RunToCompletion, _) => (v("[1]")?, Some("a")),
                    (ExecutionMode::Suspendable, false) => (v("[2]")?, Some("b")),
                    (ExecutionMode::Suspendable, true) => (Value::Undefined, None),
                };
                for dest in [1, 2] {
                    assert_eq!(vm.get_register(dest)?, &expected_value);
                    if recording {
                        let expected_origin = key.map_or(RuntimeOrigin::Unknown, |key| {
                            source(vm.explain.origins.epoch, vec![PathSegment::Key(key.into())])
                        });
                        assert_eq!(vm.explain.origins.get(dest), expected_origin);
                    }
                }
            }
        }
    }
    Ok(())
}

#[test]
#[allow(clippy::panic_in_result_fn)]
fn g2_accumulated_returns_and_cache_do_not_cross_capture_epochs() -> Result<()> {
    use super::super::execution_model::FrameKind;
    let program = (*compile(
        "package t\np := input.a\n\
         p := input.b if { __builtin_host_await(true,\"pause\") }\nr := [p,p]\n",
    )?)
    .clone();
    let p = g2_rule(&program, "data.t.p")?;
    assert!(
        !program
            .rule_infos
            .get(usize::from(p))
            .context("fixture rule")?
            .early_exit_on_first_success
    );
    let mut cached = program.clone();
    let after = g2_literal(&mut cached, r#""after-cache""#)?;
    let cached = g2_driver(
        cached,
        vec![
            Instruction::LoadInput { dest: 0 },
            Instruction::CallRule {
                dest: 1,
                rule_index: p,
            },
            Instruction::LoadTrue { dest: 13 },
            Instruction::Load {
                dest: 14,
                literal_idx: after,
            },
            Instruction::HostAwait {
                dest: 12,
                arg: 13,
                id: 14,
            },
            Instruction::CallRule {
                dest: 2,
                rule_index: p,
            },
        ],
    );
    let program = g2_driver(
        program,
        vec![
            Instruction::LoadInput { dest: 0 },
            Instruction::Move { dest: 10, src: 0 },
            Instruction::CallRule {
                dest: 1,
                rule_index: p,
            },
            Instruction::CallRule {
                dest: 2,
                rule_index: p,
            },
        ],
    );
    let input = v(r#"{"a":[1],"b":[1]}"#)?;
    for recording in [false, true] {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for scenario in ["keep", "replace", "input", "data", "late", "abort"] {
                if mode == ExecutionMode::RunToCompletion && scenario != "keep" {
                    continue;
                }
                let mut vm = g2_vm(program.clone(), input.clone(), mode, recording);
                if mode == ExecutionMode::RunToCompletion {
                    vm.set_host_await_responses([(v(r#""pause""#)?, vec![Value::Bool(true)])]);
                    g2_execute(&mut vm)?;
                } else {
                    vm.execute_entry_point_by_index(0)?;
                    assert_eq!(vm.get_host_await_identifier(), Some(&v(r#""pause""#)?));
                    let accumulated = (0..vm.execution_stack.len()).find_map(|index| {
                        match vm.execution_stack.get(index)?.kind {
                            FrameKind::Rule(ref data) if data.rule_index == p => {
                                data.accumulated_result.as_ref()
                            }
                            _ => None,
                        }
                    });
                    assert_eq!(accumulated, Some(&v("[1]")?));
                    match scenario {
                        "replace" if recording => vm.set_explanation_recorder(Box::new(Recorder)),
                        "input" => vm.set_input(input.clone()),
                        "data" => vm.set_data(v("{}")?)?,
                        "late" => {
                            vm.take_explanation_recorder();
                            vm.set_explanation_recorder(Box::new(Recorder));
                        }
                        "abort" => vm.set_max_instructions(1),
                        _ => {}
                    }
                    let resumed = vm.resume(Some(Value::Bool(true)));
                    if scenario == "abort" {
                        assert!(matches!(
                            resumed,
                            Err(super::super::errors::VmError::InstructionLimitExceeded { .. })
                        ));
                        assert!(vm.explain.origins.registers.is_empty());
                        assert!(vm.explain.origins.windows.is_empty());
                        continue;
                    }
                    resumed?;
                    assert!(
                        matches!(vm.execution_state(), ExecutionState::Completed { result } if result == &Value::Bool(true))
                    );
                    assert!(vm.explain.origins.windows.is_empty());
                }
                assert_eq!(vm.get_register(10)?, &input);
                assert_eq!(
                    vm.explain.origins.get(10),
                    if recording && scenario == "keep" {
                        source(vm.explain.origins.epoch, vec![])
                    } else {
                        RuntimeOrigin::Unknown
                    }
                );
                for dest in [1, 2] {
                    assert_eq!(vm.get_register(dest)?, &v("[1]")?);
                    let expected = if recording && scenario == "keep" {
                        source(vm.explain.origins.epoch, vec![PathSegment::Key("a".into())])
                    } else {
                        RuntimeOrigin::Unknown
                    };
                    assert_eq!(vm.explain.origins.get(dest), expected);
                }
                if !vm.explain_enabled() {
                    assert!(vm.explain.origins.registers.is_empty());
                }
                let epoch = vm.explain.origins.epoch;
                vm.set_input(v(r#"{"a":[2],"b":[2]}"#)?);
                if mode == ExecutionMode::RunToCompletion {
                    vm.set_host_await_responses([(v(r#""pause""#)?, vec![Value::Bool(true)])]);
                    g2_execute(&mut vm)?;
                } else {
                    vm.execute_entry_point_by_index(0)?;
                    assert_eq!(vm.get_host_await_identifier(), Some(&v(r#""pause""#)?));
                    vm.resume(Some(Value::Bool(true)))?;
                }
                assert_ne!(vm.explain.origins.epoch, epoch);
                assert_eq!(vm.get_register(10)?, &v(r#"{"a":[2],"b":[2]}"#)?);
                if vm.explain_enabled() {
                    assert_eq!(
                        vm.explain.origins.get(10),
                        source(vm.explain.origins.epoch, vec![])
                    );
                }
                for dest in [1, 2] {
                    assert_eq!(vm.get_register(dest)?, &v("[2]")?);
                    if vm.explain_enabled() {
                        assert_eq!(
                            vm.explain.origins.get(dest),
                            source(vm.explain.origins.epoch, vec![PathSegment::Key("a".into())])
                        );
                    }
                }
            }
        }
    }
    for install in [false, true] {
        let mut vm = g2_vm(
            cached.clone(),
            input.clone(),
            ExecutionMode::Suspendable,
            false,
        );
        vm.execute_entry_point_by_index(0)?;
        assert_eq!(vm.get_host_await_identifier(), Some(&v(r#""pause""#)?));
        vm.resume(Some(Value::Bool(true)))?;
        assert_eq!(
            vm.get_host_await_identifier(),
            Some(&v(r#""after-cache""#)?)
        );
        let cache_entry = vm
            .rule_cache
            .get(usize::from(p))
            .context("fixture cached rule")?;
        assert!(cache_entry.0);
        assert_eq!(cache_entry.1, v("[1]")?);
        if install {
            vm.set_explanation_recorder(Box::new(Recorder));
        }
        vm.resume(Some(Value::Bool(true)))?;
        assert!(
            matches!(vm.execution_state(), ExecutionState::Completed { result } if result == &Value::Bool(true))
        );
        assert_eq!(vm.get_register(2)?, &v("[1]")?);
        assert_eq!(vm.explain.origins.get(2), RuntimeOrigin::Unknown);
        assert!(vm.explain.origins.windows.is_empty());
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
    program.dispatch_window_size = 6;
    program.literals = vec![v("0")?, v("4294967296")?];
    let constructed = program.instruction_data.add_array_create_params(
        crate::rvm::instructions::ArrayCreateParams {
            dest: 3,
            elements: vec![1],
        },
    );
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
        instruction(
            &mut vm,
            &program,
            Instruction::ArrayCreate {
                params_index: constructed,
            },
        )?;
        for (dest, literal_idx) in [(4, 0), (5, 1)] {
            instruction(
                &mut vm,
                &program,
                Instruction::IndexLiteral {
                    dest,
                    container: 3,
                    literal_idx,
                },
            )?;
        }
        assert_eq!(vm.get_register(1)?, &v("[]")?);
        assert_eq!(vm.get_register(4)?, vm.get_register(1)?);
        assert_eq!(vm.get_register(5)?, vm.get_register(2)?);
        let overflow_value = vm.get_register(2)?.clone();
        #[cfg(target_pointer_width = "32")]
        assert_eq!(overflow_value, v("[]")?);
        #[cfg(target_pointer_width = "64")]
        assert_eq!(overflow_value, Value::Undefined);
        if recording {
            assert_eq!(Some(overflow_value), baseline);
            let zero_origin = source(vm.explain.origins.epoch, vec![PathSegment::Index(0)]);
            assert_eq!(vm.explain.origins.get(1), zero_origin);
            assert_eq!(vm.explain.origins.get(4), zero_origin);
            let overflow_origin = vm.explain.origins.get(2);
            assert_eq!(overflow_origin, RuntimeOrigin::Unknown);
            assert_eq!(vm.explain.origins.get(5), RuntimeOrigin::Unknown);
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
