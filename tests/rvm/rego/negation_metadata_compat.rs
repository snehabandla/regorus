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
        let json = Program::deserialize_json(&program.serialize_json().map_err(anyhow::Error::msg)?)
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
                    assert_eq!(results.first(), results.get(1), "instruction budget {limit}");
                }
            }
        }
    }
    Ok(())
}
