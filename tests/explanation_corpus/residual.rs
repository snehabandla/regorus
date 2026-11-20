// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::*;
use regorus::explain::{PartialEvalSettings, PathSegment, UnknownPath, UnknownRoot};
use serde_json::json;

// Decode the structured wire fields, not presentation text. Values keep the
// engine's numeric equality and ordering rather than going through f64.
#[derive(Deserialize)]
struct Report {
    kind: String,
    status: ExpectedResidualStatus,
    #[serde(default = "undefined")]
    result: Value,
    residual_queries: Vec<Alternative>,
}

#[derive(Deserialize)]
struct Alternative {
    #[serde(default, deserialize_with = "present")]
    key: Option<Value>,
    #[serde(default = "undefined")]
    value: Value,
    conditions: Vec<Condition>,
    #[serde(default = "exact")]
    status: String,
    #[serde(default, deserialize_with = "present_json")]
    unresolved: Option<serde_json::Value>,
}

#[derive(Deserialize)]
struct Condition {
    kind: String,
    operator: Option<String>,
    input_path: Option<String>,
    #[serde(default, deserialize_with = "present")]
    value: Option<Value>,
    #[serde(default)]
    negated: Vec<Condition>,
    #[serde(default, deserialize_with = "present_json")]
    call: Option<serde_json::Value>,
}

fn undefined() -> Value {
    Value::Undefined
}

fn exact() -> String {
    "exact".into()
}

fn present_json<'de, D: serde::Deserializer<'de>>(
    d: D,
) -> Result<Option<serde_json::Value>, D::Error> {
    serde_json::Value::deserialize(d).map(Some)
}

/// The corpus supports input-rooted dotted keys, JSON-quoted bracket keys and
/// unsigned indices. Dynamic references and other roots fail closed.
pub(super) fn input_path(text: &str) -> Result<UnknownPath> {
    let mut rest = text
        .strip_prefix("input")
        .context("path is not input-rooted")?;
    let mut segments = Vec::new();
    while !rest.is_empty() {
        if let Some(tail) = rest.strip_prefix('.') {
            let end = tail.find(['.', '[']).unwrap_or(tail.len());
            let key = &tail[..end];
            if key.is_empty()
                || !key.bytes().enumerate().all(|(i, b)| {
                    b.is_ascii_alphabetic() || b == b'_' || (i > 0 && b.is_ascii_digit())
                })
            {
                bail!("invalid dotted key in {text}");
            }
            segments.push(PathSegment::Key(key.into()));
            rest = &tail[end..];
        } else if let Some(tail) = rest.strip_prefix('[') {
            let mut stream =
                serde_json::Deserializer::from_str(tail).into_iter::<serde_json::Value>();
            let item = stream.next().context("missing bracket segment")??;
            rest = tail[stream.byte_offset()..]
                .strip_prefix(']')
                .context("unclosed bracket")?;
            segments.push(match item {
                serde_json::Value::String(key) => PathSegment::Key(key),
                serde_json::Value::Number(index) => {
                    PathSegment::Index(index.as_u64().context("index is not unsigned")?)
                }
                _ => bail!("unsupported path segment"),
            });
        } else {
            bail!("invalid path {text}");
        }
    }
    Ok(UnknownPath::new(UnknownRoot::Input, segments))
}

fn segment_key(segment: &PathSegment) -> Result<Value> {
    match segment {
        PathSegment::Key(key) => Ok(Value::from(key.as_str())),
        PathSegment::Index(index) => Ok(Value::from(*index)),
        _ => bail!("unsupported path segment"),
    }
}

fn lookup(input: &Value, path: &UnknownPath) -> Result<Value> {
    let mut value = input;
    for segment in &path.segments {
        value = &value[&segment_key(segment)?];
    }
    Ok(value.clone())
}

fn remove_unknown(input: &mut Value, segments: &[PathSegment]) -> Result<()> {
    let Some((first, remaining)) = segments.split_first() else {
        *input = Value::Undefined;
        return Ok(());
    };
    let key = segment_key(first)?;
    let child = match input {
        Value::Object(_) => {
            let object = input.as_object_mut()?;
            if remaining.is_empty() {
                object.remove(&key);
                return Ok(());
            }
            object.get_mut(&key)
        }
        Value::Array(_) => match first {
            PathSegment::Index(index) => input
                .as_array_mut()?
                .get_mut(usize::try_from(*index)?),
            PathSegment::Key(_) => None,
            _ => bail!("unsupported path segment"),
        },
        Value::Undefined | Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => {
            None
        }
        _ => bail!("cannot remove an unknown from this input container"),
    };
    if let Some(child) = child {
        remove_unknown(child, remaining)?;
    }
    Ok(())
}

impl Condition {
    fn validate(&self) -> Result<()> {
        if self.call.is_some() {
            bail!("residual calls are not supported by this checker");
        }
        match self.kind.as_str() {
            "negation_holds"
                if self.operator.is_none() && self.input_path.is_none() && self.value.is_none() =>
            {
                for condition in &self.negated {
                    condition.validate()?;
                }
            }
            "exists" | "truthy" | "condition_holds" if self.negated.is_empty() => {
                input_path(
                    self.input_path
                        .as_deref()
                        .context("missing structured path")?,
                )?;
                if self.kind == "condition_holds" {
                    match self.operator.as_deref() {
                        Some("==" | "!=" | "<" | "<=" | ">" | ">=") => {}
                        _ => bail!("unsupported residual operator"),
                    }
                    if matches!(self.value, None | Some(Value::Undefined)) {
                        bail!("missing structured comparison value");
                    }
                } else if self.operator.is_some() || self.value.is_some() {
                    bail!("unexpected comparison fields");
                }
            }
            _ => bail!("unsupported residual kind or fields: {}", self.kind),
        }
        Ok(())
    }

    fn holds(&self, input: &Value) -> Result<bool> {
        if self.kind == "negation_holds" {
            return Ok(!all_hold(&self.negated, input)?);
        }
        let value = lookup(
            input,
            &input_path(self.input_path.as_deref().context("missing path")?)?,
        )?;
        if value == Value::Undefined {
            return Ok(false);
        }
        Ok(match self.kind.as_str() {
            "exists" => true,
            "truthy" => value != Value::Bool(false),
            "condition_holds" => {
                let known = self.value.as_ref().context("missing value")?;
                match self.operator.as_deref() {
                    Some("==") => value == *known,
                    Some("!=") => value != *known,
                    Some("<") => value < *known,
                    Some("<=") => value <= *known,
                    Some(">") => value > *known,
                    Some(">=") => value >= *known,
                    _ => bail!("unsupported operator"),
                }
            }
            _ => bail!("unsupported kind"),
        })
    }
}

fn all_hold(conditions: &[Condition], input: &Value) -> Result<bool> {
    for condition in conditions {
        if !condition.holds(input)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn apply(report: &Report, input: &Value) -> Result<Value> {
    if report.status != ExpectedResidualStatus::Exact {
        bail!("non-exact residual is not executable");
    }
    if !matches!(
        report.kind.as_str(),
        "complete" | "function" | "partial_set" | "partial_object"
    ) {
        bail!("unsupported rule kind");
    }
    if report.result != Value::Undefined && !report.residual_queries.is_empty() {
        bail!("concrete result with residual alternatives");
    }
    // Validate even untaken alternatives: an unknown operator must never be
    // hidden by a false conjunct or an earlier successful else branch.
    for alternative in &report.residual_queries {
        if alternative.status != "exact"
            || alternative.unresolved.is_some()
            || alternative.value == Value::Undefined
            || (report.kind == "partial_object") != alternative.key.is_some()
            || alternative.key == Some(Value::Undefined)
        {
            bail!("malformed exact alternative");
        }
        for condition in &alternative.conditions {
            condition.validate()?;
        }
    }
    if report.residual_queries.is_empty() && report.result != Value::Undefined {
        return Ok(report.result.clone());
    }
    let mut set = BTreeSet::new();
    let mut object = BTreeMap::new();
    for alternative in &report.residual_queries {
        if !all_hold(&alternative.conditions, input)? {
            continue;
        }
        match report.kind.as_str() {
            "complete" | "function" => return Ok(alternative.value.clone()),
            "partial_set" => {
                set.insert(alternative.value.clone());
            }
            "partial_object" => {
                let key = alternative.key.as_ref().context("missing object key")?;
                if let Some(previous) = object.insert(key.clone(), alternative.value.clone()) {
                    if previous != alternative.value {
                        bail!("conflicting residual object values");
                    }
                }
            }
            _ => bail!("unsupported rule kind"),
        }
    }
    Ok(match report.kind.as_str() {
        "complete" | "function" => Value::Undefined,
        "partial_set" => Value::from(set),
        "partial_object" => Value::from(object),
        _ => bail!("unsupported rule kind"),
    })
}

fn check_completion(report: &Report, example: &Example) -> Result<()> {
    let actual = Ok(apply(
        report,
        &example.input.clone().unwrap_or(Value::Undefined),
    )?);
    let expected = Outcome::from_want(&example.want_result, &example.want_error)?;
    if !expected.matches(&actual) {
        bail!("expected {expected:?}, got {}", describe(&actual));
    }
    Ok(())
}

fn decode(pe: regorus::explain::PartialEvalResult) -> Result<Report> {
    let mut report: Report = serde_json::from_value(serde_json::to_value(&pe)?)?;
    // Concrete sets/non-string-keyed objects need the typed value;
    // only residual operands are required to be JSON-lossless.
    report.result = pe.result;
    Ok(report)
}

#[test_resources("tests/explanation_corpus/cases/*.yaml")]
fn corpus_partial_eval(file: &str) {
    run_partial_file(file).unwrap();
}

fn run_partial_file(file: &str) -> Result<()> {
    for case in load(Path::new(file))?.cases {
        let Some(expected) = &case.partial_eval else {
            continue;
        };
        for example in &case.examples {
            let check = || -> Result<()> {
                let mut settings = PartialEvalSettings::default();
                settings.unknowns = case
                    .unknowns
                    .iter()
                    .map(|p| input_path(p))
                    .collect::<Result<_>>()?;
                let mut input = example.input.clone().unwrap_or(Value::Undefined);
                for unknown in &settings.unknowns {
                    remove_unknown(&mut input, &unknown.segments)?;
                }
                let mut engine = new_engine(&case, example)?;
                let compiled = engine.compile_with_entrypoint(&case.query.as_str().into())?;
                let mut vm = RegoVM::new();
                vm.load_program(Compiler::compile_from_policy(
                    &compiled,
                    &[case.query.as_str()],
                )?);
                vm.set_data(engine.get_data())?;
                vm.set_input(input);
                vm.set_strict_builtin_errors(case.strict_builtin_errors);
                vm.set_partial_eval_settings(settings);
                let pe = vm.partial_eval(&case.query)?;
                let report = decode(pe)?;
                if report.status != expected.status {
                    bail!("expected {:?}, got {:?}", expected.status, report.status);
                }
                if report.status == ExpectedResidualStatus::Exact {
                    if let Some(count) = expected.alternatives {
                        if count != report.residual_queries.len() {
                            bail!(
                                "expected {count} alternatives, got {}",
                                report.residual_queries.len()
                            );
                        }
                    }
                    check_completion(&report, example)?;
                } else if matches!(
                    report.status,
                    ExpectedResidualStatus::Unsupported | ExpectedResidualStatus::PossibleConflict
                ) && (report.result != Value::Undefined
                    || !report.residual_queries.is_empty())
                {
                    bail!("non-exact report exposes an outcome");
                }
                Ok(())
            };
            check().with_context(|| format!("{}/{}", case.note, example.note))?;
        }
    }
    Ok(())
}

fn fixture(kind: &str, alternatives: serde_json::Value) -> Result<Report> {
    Ok(serde_json::from_value(json!({
        "kind": kind, "status": "exact", "residual_queries": alternatives
    }))?)
}

#[test]
fn residual_contract_fixtures() -> Result<()> {
    // These are the #876 complete/set/object examples in src/explain/fixtures.rs.
    let role = json!({"text": "not executable Rego", "kind": "condition_holds",
        "operator": "==", "input_path": "input.role", "value": "admin"});
    let locked = json!({"kind": "truthy", "input_path": "input.locked"});
    let complete = fixture(
        "complete",
        json!([
            {"value": true, "conditions": [role]},
            {"value": true, "conditions": [{"kind": "negation_holds", "negated": [locked]}]}
        ]),
    )?;
    for (input, want) in [
        (r#"{"role":"admin","locked":true}"#, Value::Bool(true)),
        (r#"{"role":"guest","locked":false}"#, Value::Bool(true)),
        (r#"{"role":"guest","locked":true}"#, Value::Undefined),
    ] {
        assert_eq!(apply(&complete, &Value::from_json_str(input)?)?, want);
    }
    let set = fixture(
        "partial_set",
        json!([
            {"value": "admin", "conditions": [role]},
            {"value": "locked", "conditions": [locked]},
            {"value": "admin", "conditions": [role]}
        ]),
    )?;
    assert_eq!(
        apply(
            &set,
            &Value::from_json_str(r#"{"role":"admin","locked":true}"#)?
        )?,
        process_value(&Value::from_json_str(r#"{"set!":["admin","locked"]}"#)?)?
    );
    assert_eq!(
        apply(
            &set,
            &Value::from_json_str(r#"{"role":"guest","locked":false}"#)?
        )?,
        Value::new_set()
    );
    let object = fixture(
        "partial_object",
        json!([{"key": "env", "value": "prod",
        "conditions": [{"kind": "condition_holds", "operator": "==",
            "input_path": "input.env", "value": "prod"}]}]),
    )?;
    assert_eq!(
        apply(&object, &Value::from_json_str(r#"{"env":"prod"}"#)?)?,
        Value::from_json_str(r#"{"env":"prod"}"#)?
    );
    assert_eq!(
        apply(&object, &Value::from_json_str(r#"{"env":"dev"}"#)?)?,
        Value::new_object()
    );
    let ordered = fixture(
        "function",
        json!([
            {"value":"gold","conditions":[role]}, {"value":"basic","conditions":[]}
        ]),
    )?;
    assert_eq!(
        apply(&ordered, &Value::from_json_str(r#"{"role":"admin"}"#)?)?,
        Value::from("gold")
    );
    assert_eq!(apply(&ordered, &Value::new_object())?, Value::from("basic"));
    Ok(())
}

#[test]
fn residual_rejects_wrong_answers_and_unknown_semantics() -> Result<()> {
    let corpus = load(Path::new(CASES_DIR).join("rules.yaml").as_path())?;
    let case = corpus.cases.first().context("missing two-condition case")?;
    let example = case.examples.first().context("missing matching example")?;
    let mut report = fixture(
        "complete",
        json!([{"value": true, "conditions": [
            {"kind":"condition_holds","operator":"==","input_path":"input.user.role","value":"guest"},
            {"kind":"condition_holds","operator":"==","input_path":"input.action","value":"delete"}
        ]}]),
    )?;
    assert!(
        check_completion(&report, example).is_err(),
        "wrong residual must fail the oracle"
    );
    let alternative = report
        .residual_queries
        .first_mut()
        .context("missing alternative")?;
    alternative
        .conditions
        .first_mut()
        .context("missing condition")?
        .operator = Some("??".into());
    assert!(
        apply(&report, &Value::new_object()).is_err(),
        "undefined input cannot hide unknown operator"
    );
    let mut report = fixture(
        "complete",
        json!([
            {"value":true,"conditions":[]}, {"value":true,"conditions":[
                {"kind":"future_condition","input_path":"input.x"}]}
        ]),
    )?;
    assert!(
        apply(&report, &Value::new_object()).is_err(),
        "first match cannot hide unknown kind"
    );
    report.kind = "future_rule".into();
    assert!(apply(&report, &Value::new_object()).is_err());
    for condition in [
        json!({"kind":"condition_holds","operator":"==","value":1,"text":"input.x == 1"}),
        json!({"kind":"condition_holds","operator":"==","input_path":"input.x","text":"input.x == 1"}),
        json!({"kind":"condition_holds","operator":"in","input_path":"input.x","value":[1]}),
    ] {
        let report = fixture("complete", json!([{"value":true,"conditions":[condition]}]))?;
        assert!(apply(&report, &Value::new_object()).is_err());
    }
    let mut case = load(Path::new(CASES_DIR).join("rules.yaml").as_path())?
        .cases
        .remove(0);
    case.partial_eval = None;
    assert!(
        check_case_shape(&case).is_err(),
        "unknown-input cases require PE expectations"
    );
    Ok(())
}

#[test]
fn residual_paths_null_and_numeric_precision() -> Result<()> {
    let report = fixture(
        "complete",
        json!([{"value": false, "conditions": [
            {"kind":"condition_holds","operator":">","input_path":"input.rows[0][\"0\"]",
                "value":9007199254740992_u64},
            {"kind":"condition_holds","operator":"==","input_path":"input[\"a.b\\\"[c]\"]","value":null}
        ]}]),
    )?;
    for (number, want) in [
        ("9007199254740993", Value::Bool(false)),
        ("9007199254740992", Value::Undefined),
        ("9007199254740992.0", Value::Undefined),
    ] {
        let input =
            Value::from_json_str(&format!(r#"{{"rows":[{{"0":{number}}}],"a.b\"[c]":null}}"#))?;
        assert_eq!(apply(&report, &input)?, want);
    }
    let mut input = Value::from_json_str(r#"{"rows":[{"0":1,"keep":2}],"a.b":3,"a":{"b":4}}"#)?;
    remove_unknown(&mut input, &input_path(r#"input.rows[0]["0"]"#)?.segments)?;
    remove_unknown(&mut input, &input_path(r#"input["a.b"]"#)?.segments)?;
    assert_eq!(
        input,
        Value::from_json_str(r#"{"rows":[{"keep":2}],"a":{"b":4}}"#)?
    );
    for path in [
        "inputx",
        "input.a..b",
        "input[-1]",
        "input[_]",
        "data.a",
        "context.a",
    ] {
        assert!(input_path(path).is_err(), "{path}");
    }
    Ok(())
}

#[test]
fn residual_unknown_pruning_distinguishes_array_indices_and_string_keys() -> Result<()> {
    let mut array = Value::from_json_str(r#"{"rows":[1]}"#)?;
    remove_unknown(&mut array, &input_path("input.rows[0]")?.segments)?;
    assert_eq!(array["rows"].as_array()?.len(), 1);
    assert_eq!(array["rows"][0], Value::Undefined);

    let mut object = Value::from_json_str(r#"{"rows":{"0":1,"keep":2}}"#)?;
    remove_unknown(&mut object, &input_path(r#"input.rows["0"]"#)?.segments)?;
    assert_eq!(object, Value::from_json_str(r#"{"rows":{"keep":2}}"#)?);

    let original = Value::from_json_str(r#"{"rows":[1]}"#)?;
    let path = input_path(r#"input.rows["0"]"#)?;
    assert_eq!(lookup(&original, &path)?, Value::Undefined);
    let mut array = original.clone();
    remove_unknown(&mut array, &path.segments)?;
    assert_eq!(array, original);
    Ok(())
}

#[test]
fn residual_native_constant_without_json_range_or_parser_limits() -> Result<()> {
    use regorus::explain::ResidualStatus;
    use regorus::rvm::{Instruction, Program};

    let ten = Value::from(10_u64);
    let mut huge = Value::from(1_u64);
    for _ in 0..400 {
        huge = Value::from(huge.as_number()?.mul(ten.as_number()?)?);
    }
    let mut program = Program::new();
    program.max_rule_window_size = 1;
    program.dispatch_window_size = 1;
    program.literals.push(huge.clone());
    program.add_instruction(Instruction::Load { dest: 0, literal_idx: 0 }, None);
    program.add_instruction(Instruction::Return { value: 0 }, None);
    program.add_entry_point("data.test.answer".into(), 0);
    let mut vm = RegoVM::new();
    vm.load_program(std::sync::Arc::new(program));
    vm.set_input(Value::new_object());
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = vec![UnknownPath::input_keys(["u"])];
    vm.set_partial_eval_settings(settings);
    let pe = vm.partial_eval("data.test.answer")?;
    assert_eq!(pe.status, ResidualStatus::Exact);
    assert_eq!(pe.result, huge);
    assert!(pe.residual_queries.is_empty());
    let report = decode(pe)?;
    assert_eq!(apply(&report, &Value::new_object())?, huge);
    Ok(())
}
