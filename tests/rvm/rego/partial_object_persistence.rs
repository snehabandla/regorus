// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use regorus::rvm::instructions::ObjectDeepSetParams;
use regorus::rvm::program::Program;
use regorus::Value;

#[test]
fn review_json_native_literals() {
    let mut object = Value::new_object();
    object
        .as_object_mut()
        .unwrap()
        .insert(Value::from(vec![Value::from(1u64)]), Value::new_set());
    let mut program = Program::new();
    program.literals = vec![object, Value::Undefined, Value::from("ordinary")];
    let json = program.serialize_json().unwrap();
    let restored = Program::deserialize_json(&json).unwrap();
    assert_eq!(restored.literals, program.literals);

    let mut malformed: serde_json::Value = serde_json::from_str(&json).unwrap();
    malformed["typed_literals"] = serde_json::json!([[255]]);
    assert!(Program::deserialize_json(&malformed.to_string()).is_err());
}

#[test]
fn review_json_parameter_table_limit() {
    let mut program = Program::new();
    let params = ObjectDeepSetParams {
        obj: 0,
        keys: vec![1],
        value: 2,
        multi_value: false,
    };
    program.instruction_data.object_deep_set_params =
        vec![params.clone(); usize::from(u16::MAX) + 1];
    let mut json: serde_json::Value =
        serde_json::from_str(&program.serialize_json().unwrap()).unwrap();
    Program::deserialize_json(&json.to_string()).unwrap();
    program.instruction_data.object_deep_set_params.push(params);
    assert!(program.serialize_json().is_err());
    let extra = json["instruction_data"]["object_deep_set_params"][0].clone();
    json["instruction_data"]["object_deep_set_params"]
        .as_array_mut()
        .unwrap()
        .push(extra);
    assert!(Program::deserialize_json(&json.to_string()).is_err());
}

#[test]
fn review_binary_parameter_table_limit() {
    let mut program = Program::new();
    let params = ObjectDeepSetParams {
        obj: 0,
        keys: vec![1],
        value: 2,
        multi_value: false,
    };
    program.instruction_data.object_deep_set_params =
        vec![params.clone(); usize::from(u16::MAX) + 1];
    let mut blob = program.serialize_binary().unwrap();
    assert!(matches!(
        Program::deserialize_binary(&blob).unwrap(),
        regorus::rvm::program::DeserializationResult::Complete(_)
    ));
    let preamble: usize = [8, 12, 16, 20]
        .iter()
        .map(|offset| {
            usize::try_from(u32::from_le_bytes(
                blob[*offset..*offset + 4].try_into().unwrap(),
            ))
            .unwrap()
        })
        .sum();
    blob.truncate(25 + preamble);
    program.instruction_data.object_deep_set_params.push(params);
    let core = postcard::to_allocvec(&program).unwrap();
    blob.extend_from_slice(&u32::try_from(core.len()).unwrap().to_le_bytes());
    blob.extend_from_slice(&core);
    assert!(Program::deserialize_binary(&blob).is_err());
}

fn nested_array(depth: usize) -> Value {
    (0..depth).fold(Value::Null, |value, _| Value::from(vec![value]))
}

#[test]
fn review_typed_literal_depth_limit() {
    for (depth, accepted) in [(100, true), (200, false)] {
        let mut program = Program::new();
        program.literals = vec![nested_array(depth)];
        let json = program.serialize_json().unwrap();
        let restored = Program::deserialize_json(&json);
        assert_eq!(restored.is_ok(), accepted, "JSON depth {depth}");
        if let Ok(restored) = restored {
            assert_eq!(restored.literals, program.literals);
        } else if let Err(error) = restored {
            // serde_json's own recursion limit may reject the untyped copy first.
            assert!(
                error.contains("nesting depth") || error.contains("recursion limit"),
                "{error}"
            );
        }
        let blob = program.serialize_binary().unwrap();
        // An undecodable binary literal section requires recompilation.
        assert_eq!(
            matches!(
                Program::deserialize_binary(&blob).unwrap(),
                regorus::rvm::program::DeserializationResult::Complete(_)
            ),
            accepted,
            "binary depth {depth}"
        );
    }

    // A forged literal nested far beyond the limit is rejected instead of
    // exhausting the stack: postcard Array variant (4) of length 1, repeated.
    for (depth, accepted) in [(100, true), (1_000_000, false)] {
        let mut bytes = [4u8, 1].repeat(depth);
        bytes.push(0);
        let mut json: serde_json::Value =
            serde_json::from_str(&Program::new().serialize_json().unwrap()).unwrap();
        json["typed_literals"] = serde_json::json!([bytes]);
        match Program::deserialize_json(&json.to_string()) {
            Ok(program) => {
                assert!(accepted, "forged depth {depth}");
                assert_eq!(program.literals, vec![nested_array(depth)]);
            }
            Err(error) => {
                assert!(!accepted, "forged depth {depth}: {error}");
                assert!(error.contains("Invalid typed literal"), "{error}");
            }
        }
    }
}

#[test]
fn review_typed_literal_trailing_bytes() {
    let mut program = Program::new();
    program.literals = vec![Value::from(vec![Value::from(1u64)]), Value::new_set()];
    let mut json: serde_json::Value =
        serde_json::from_str(&program.serialize_json().unwrap()).unwrap();
    Program::deserialize_json(&json.to_string()).unwrap();
    json["typed_literals"][0]
        .as_array_mut()
        .unwrap()
        .push(0.into());
    let error = Program::deserialize_json(&json.to_string()).unwrap_err();
    assert!(error.contains("trailing bytes"), "{error}");
}

#[test]
fn review_object_deep_set_without_keys_rejected_at_load() {
    let mut program = Program::new();
    program.instruction_data.object_deep_set_params = vec![ObjectDeepSetParams {
        obj: 0,
        keys: vec![1],
        value: 2,
        multi_value: false,
    }];
    let mut json: serde_json::Value =
        serde_json::from_str(&program.serialize_json().unwrap()).unwrap();
    Program::deserialize_json(&json.to_string()).unwrap();
    json["instruction_data"]["object_deep_set_params"][0]["keys"] = serde_json::json!([]);
    let error = Program::deserialize_json(&json.to_string()).unwrap_err();
    assert!(error.contains("at least one key"), "{error}");

    let mut blob = program.serialize_binary().unwrap();
    assert!(Program::deserialize_binary(&blob).is_ok());
    let preamble: usize = [8, 12, 16, 20]
        .iter()
        .map(|offset| {
            usize::try_from(u32::from_le_bytes(
                blob[*offset..*offset + 4].try_into().unwrap(),
            ))
            .unwrap()
        })
        .sum();
    blob.truncate(25 + preamble);
    program.instruction_data.object_deep_set_params[0]
        .keys
        .clear();
    let core = postcard::to_allocvec(&program).unwrap();
    blob.extend_from_slice(&u32::try_from(core.len()).unwrap().to_le_bytes());
    blob.extend_from_slice(&core);
    assert!(Program::deserialize_binary(&blob).is_err());
}
