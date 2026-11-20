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
    #[serde(default)]
    status: Option<String>,
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
    call: Option<serde_json::Value>,
}

fn undefined() -> Value {
    Value::Undefined
}

/// The corpus supports input-rooted dotted keys, JSON-quoted bracket keys and
/// unsigned indices. Dynamic references and other roots fail closed.
fn input_path(text: &str) -> Result<UnknownPath> {
    let mut rest = text.strip_prefix("input").context("path is not input-rooted")?;
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
            let mut stream = serde_json::Deserializer::from_str(tail).into_iter::<serde_json::Value>();
            let item = stream.next().context("missing bracket segment")??;
            rest = tail[stream.byte_offset()..].strip_prefix(']').context("unclosed bracket")?;
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
        Value::Array(_) => input.as_array_mut()?.get_mut(usize::try_from(key.as_u64()?)?),
        Value::Undefined | Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => None,
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
            "negation_holds" if self.operator.is_none()
                && self.input_path.is_none() && self.value.is_none() => {
                for condition in &self.negated {
                    condition.validate()?;
                }
            }
            "exists" | "truthy" | "condition_holds" if self.negated.is_empty() => {
                input_path(self.input_path.as_deref().context("missing structured path")?)?;
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
        let value = lookup(input, &input_path(self.input_path.as_deref().context("missing path")?)?)?;
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
    if !matches!(report.kind.as_str(), "complete" | "function" | "partial_set" | "partial_object") {
        bail!("unsupported rule kind");
    }
    if report.result != Value::Undefined && !report.residual_queries.is_empty() {
        bail!("concrete result with residual alternatives");
    }
    // Validate even untaken alternatives: an unknown operator must never be
    // hidden by a false conjunct or an earlier successful else branch.
    for alternative in &report.residual_queries {
        if alternative.status.as_deref().is_some_and(|s| s != "exact")
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
            "partial_set" => { set.insert(alternative.value.clone()); }
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
    let actual = apply(report, &example.input.clone().unwrap_or(Value::Undefined));
    let expected = Outcome::from_want(&example.want_result, &example.want_error)?;
    if !expected.matches(&actual) {
        bail!("expected {expected:?}, got {}", describe(&actual));
    }
    Ok(())
}

#[test_resources("tests/explanation_corpus/cases/*.yaml")]
fn corpus_partial_eval(file: &str) -> Result<()> {
    for case in load(Path::new(file))?.cases {
        let Some(expected) = &case.partial_eval else { continue };
        for example in &case.examples {
            let check = || -> Result<()> {
                let mut settings = PartialEvalSettings::default();
                settings.unknowns = case.unknowns.iter().map(|p| input_path(p)).collect::<Result<_>>()?;
                let mut input = example.input.clone().unwrap_or(Value::Undefined);
                for unknown in &settings.unknowns {
                    remove_unknown(&mut input, &unknown.segments)?;
                }
                let mut engine = new_engine(&case, example)?;
                let compiled = engine.compile_with_entrypoint(&case.query.as_str().into())?;
                let mut vm = RegoVM::new();
                vm.load_program(Compiler::compile_from_policy(&compiled, &[case.query.as_str()])?);
                vm.set_data(engine.get_data())?;
                vm.set_input(input);
                vm.set_strict_builtin_errors(case.strict_builtin_errors);
                vm.set_partial_eval_settings(settings);
                let report: Report = serde_json::from_value(serde_json::to_value(vm.partial_eval(&case.query)?)?)?;
                if report.status != expected.status {
                    bail!("expected {:?}, got {:?}", expected.status, report.status);
                }
                if report.status == ExpectedResidualStatus::Exact {
                    if let Some(count) = expected.alternatives {
                        if count != report.residual_queries.len() {
                            bail!("expected {count} alternatives, got {}", report.residual_queries.len());
                        }
                    }
                    check_completion(&report, example)?;
                } else if report.result != Value::Undefined || !report.residual_queries.is_empty() {
                    bail!("non-exact report exposes an outcome");
                }
                Ok(())
            };
            check().with_context(|| format!("{}/{}", case.note, example.note))?;
        }
    }
    Ok(())
}
