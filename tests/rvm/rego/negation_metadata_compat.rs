// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::{
    Compiler, DeserializationResult, Engine, ExecutionMode, ExecutionState, Program, Rc, RegoVM,
    Value,
};
use anyhow::{bail, Result};
use std::sync::Arc;

fn bytecode(program: &Program) -> Result<Vec<u8>> {
    postcard::to_allocvec(&(&program.instructions, &program.instruction_spans))
        .map_err(|error| anyhow::Error::msg(error.to_string()))
}

#[test]
fn negation_annotations_preserve_feature_independent_bytecode_and_execution() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "negation.rego".into(),
        "package t\nallow if { not input.blocked }\n".into(),
    )?;
    let entry: Rc<str> = "data.t.allow".into();
    let policy = engine.compile_with_entrypoint(&entry)?;
    let original = Compiler::compile_from_policy(&policy, &["data.t.allow"])?;
    let key = "regorus.explain.negation";
    #[cfg(not(feature = "explanations"))]
    assert!(!original.metadata.annotations.contains_key(key));
    #[cfg(feature = "explanations")]
    assert!(original.metadata.annotations.contains_key(key));
    let annotated = original.as_ref().clone();
    // Disabled readers must preserve optional metadata even if capture would
    // reject it. This also exercises the unchanged version-6 carrier.
    #[cfg(not(feature = "explanations"))]
    let annotated = {
        let mut annotated = annotated;
        annotated
            .metadata
            .annotations
            .insert(key.into(), Value::from_json_str("[1,0,[]]")?);
        annotated
    };
    let mut unannotated = annotated.clone();
    unannotated.metadata.annotations.remove(key);
    let original_bytecode = bytecode(&original)?;
    for program in [&annotated, &unannotated] {
        let json =
            Program::deserialize_json(&program.serialize_json().map_err(anyhow::Error::msg)?)
                .map_err(anyhow::Error::msg)?;
        let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
        assert_eq!(binary.get(4..8), Some(6_u32.to_le_bytes().as_slice()));
        let binary = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
            DeserializationResult::Complete(program) => program,
            DeserializationResult::Partial(_) => bail!("v6 artifact unexpectedly partial"),
        };
        for restored in [json, binary] {
            assert_eq!(
                restored.metadata.annotations.get(key),
                program.metadata.annotations.get(key)
            );
            assert_eq!(bytecode(&restored)?, original_bytecode);
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                for (input, expected) in [
                    ("{}", Value::Bool(true)),
                    (r#"{"blocked":false}"#, Value::Bool(true)),
                    (r#"{"blocked":true}"#, Value::Undefined),
                ] {
                    let mut vm = RegoVM::new();
                    vm.load_program(Arc::new(restored.clone()));
                    vm.set_input(Value::from_json_str(input)?);
                    vm.set_execution_mode(mode);
                    let returned = vm.execute()?;
                    let actual = if mode == ExecutionMode::RunToCompletion {
                        returned
                    } else {
                        match vm.execution_state() {
                            ExecutionState::Completed { result } => result.clone(),
                            other => bail!("did not complete: {other:?}"),
                        }
                    };
                    assert_eq!(actual, expected);
                }
                for limit in [1, 4, 8, 16] {
                    let mut results = Vec::new();
                    for candidate in [&restored, original.as_ref()] {
                        let mut vm = RegoVM::new();
                        vm.load_program(Arc::new(candidate.clone()));
                        vm.set_input(Value::new_object());
                        vm.set_execution_mode(mode);
                        vm.set_max_instructions(limit);
                        results.push(vm.execute());
                    }
                    assert_eq!(
                        results.first(),
                        results.get(1),
                        "instruction budget {limit}"
                    );
                }
            }
        }
    }
    Ok(())
}

#[test]
fn negation_raw_unicode_and_multiline_layout_match_feature_off_execution() -> Result<()> {
    for source in [
        "package t\nallow if { x := `é`; not input.blocked }\n",
        "package t\nallow if { not\n input.blocked }\n",
    ] {
        let mut engine = Engine::new();
        engine.add_policy("layout.rego".into(), source.into())?;
        let entry: Rc<str> = "data.t.allow".into();
        let compiled_policy = engine.compile_with_entrypoint(&entry)?;
        let program = Compiler::compile_from_policy(&compiled_policy, &["data.t.allow"])?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            let returned = vm.execute()?;
            let actual = if mode == ExecutionMode::RunToCompletion {
                returned
            } else {
                match vm.execution_state() {
                    ExecutionState::Completed { result } => result.clone(),
                    other => bail!("did not complete: {other:?}"),
                }
            };
            assert_eq!(actual, Value::Bool(true));
        }
    }
    Ok(())
}

fn exchange_prefix(name: &str) -> Result<Option<std::path::PathBuf>> {
    let Some(value) = std::env::var_os(name) else {
        return Ok(None);
    };
    let prefix = std::path::PathBuf::from(value);
    anyhow::ensure!(
        !prefix.as_os_str().is_empty()
            && prefix
                .components()
                .all(|component| matches!(component, std::path::Component::Normal(_))),
        "artifact prefix must be relative and contained in the working directory"
    );
    Ok(Some(prefix))
}

#[test]
#[ignore = "requires export/import prefixes and separate feature-build processes"]
fn negation_artifact_exchange_between_feature_builds() -> Result<()> {
    let export_prefix = exchange_prefix("B29C_EXPORT_PREFIX")?;
    let import_prefix = exchange_prefix("B29C_IMPORT_PREFIX")?;
    anyhow::ensure!(
        export_prefix.is_some() || import_prefix.is_some(),
        "B29C_EXPORT_PREFIX or B29C_IMPORT_PREFIX is required"
    );
    let mut engine = Engine::new();
    engine.add_policy(
        "exchange.rego".into(),
        "package t\nhelper(x) := x\nallow if { not helper(input.blocked) }\n".into(),
    )?;
    let entry: Rc<str> = "data.t.allow".into();
    let compiled_policy = engine.compile_with_entrypoint(&entry)?;
    let local = Compiler::compile_from_policy(&compiled_policy, &["data.t.allow"])?;
    let local_bytecode = bytecode(&local)?;
    let mut artifact = if let Some(prefix) = import_prefix {
        let json =
            Program::deserialize_json(&std::fs::read_to_string(prefix.with_extension("json"))?)
                .map_err(anyhow::Error::msg)?;
        let bytes = std::fs::read(prefix.with_extension("bin"))?;
        let binary = match Program::deserialize_binary(&bytes).map_err(anyhow::Error::msg)? {
            DeserializationResult::Complete(restored) => restored,
            DeserializationResult::Partial(_) => bail!("external artifact unexpectedly partial"),
        };
        assert_eq!(
            std::fs::read(prefix.with_extension("bytecode"))?,
            local_bytecode
        );
        assert_eq!(bytecode(&json)?, local_bytecode);
        assert_eq!(bytecode(&binary)?, local_bytecode);
        assert_eq!(
            json.metadata.annotations.get("regorus.explain.negation"),
            binary.metadata.annotations.get("regorus.explain.negation"),
        );
        for candidate in [&json, &binary] {
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(Arc::new(candidate.clone()));
                vm.set_execution_mode(mode);
                let returned = vm.execute()?;
                let actual = if mode == ExecutionMode::RunToCompletion {
                    returned
                } else {
                    match vm.execution_state() {
                        ExecutionState::Completed { result } => result.clone(),
                        other => bail!("did not complete: {other:?}"),
                    }
                };
                assert_eq!(actual, Value::Bool(true));
            }
        }
        binary
    } else {
        local.as_ref().clone()
    };
    if std::env::var_os("B29C_INJECT_INVALID_FLOAT").is_some() {
        artifact.metadata.annotations.insert(
            "regorus.explain.negation".into(),
            Value::from(vec![
                Value::from(1.5_f64),
                Value::from(0_u64),
                Value::from(Vec::new()),
            ]),
        );
    }
    if let Some(prefix) = export_prefix {
        if let Some(parent) = prefix
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
        {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(
            prefix.with_extension("json"),
            artifact.serialize_json().map_err(anyhow::Error::msg)?,
        )?;
        std::fs::write(
            prefix.with_extension("bin"),
            artifact.serialize_binary().map_err(anyhow::Error::msg)?,
        )?;
        std::fs::write(prefix.with_extension("bytecode"), bytecode(&artifact)?)?;
    }
    Ok(())
}

#[test]
fn reserved_negation_float_marker_does_not_change_other_annotations_or_execution() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy("marker.rego".into(), "package t\nallow := true\n".into())?;
    let entry: Rc<str> = "data.t.allow".into();
    let compiled_policy = engine.compile_with_entrypoint(&entry)?;
    let mut program = Compiler::compile_from_policy(&compiled_policy, &["data.t.allow"])?
        .as_ref()
        .clone();
    program.metadata.annotations.insert(
        "regorus.explain.negation".into(),
        Value::from_json_str("[1.5,0,[]]")?,
    );
    program
        .metadata
        .annotations
        .insert("other_float".into(), Value::from(1.5_f64));
    let json = Program::deserialize_json(&program.serialize_json().map_err(anyhow::Error::msg)?)
        .map_err(anyhow::Error::msg)?;
    let bytes = program.serialize_binary().map_err(anyhow::Error::msg)?;
    let binary = match Program::deserialize_binary(&bytes).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(restored) => restored,
        DeserializationResult::Partial(_) => bail!("v6 marker artifact unexpectedly partial"),
    };
    assert_eq!(
        json.metadata.annotations.get("other_float"),
        Some(&Value::from(1.5_f64))
    );
    assert_eq!(
        binary.metadata.annotations.get("other_float"),
        Some(&Value::from(1_u64))
    );
    for restored in [json, binary] {
        assert_eq!(
            restored
                .metadata
                .annotations
                .get("regorus.explain.negation"),
            Some(&Value::from(
                "regorus.explain.negation:invalid_representation"
            )),
        );
        assert_eq!(bytecode(&restored)?, bytecode(&program)?);
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(Arc::new(restored.clone()));
            vm.set_execution_mode(mode);
            let returned = vm.execute()?;
            let actual = if mode == ExecutionMode::RunToCompletion {
                returned
            } else {
                match vm.execution_state() {
                    ExecutionState::Completed { result } => result.clone(),
                    other => bail!("did not complete: {other:?}"),
                }
            };
            assert_eq!(actual, Value::Bool(true));
        }
    }
    Ok(())
}
