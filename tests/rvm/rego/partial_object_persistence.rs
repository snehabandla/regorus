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
