// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::common::{
    from_c_str, to_ref, to_regorus_result, to_shared_ref, RegorusBuffer, RegorusResult,
    RegorusStatus,
};
use crate::compile::RegorusPolicyModule;
use crate::compiled_policy::RegorusCompiledPolicy;
use crate::limits::RegorusExecutionTimerConfig;
use crate::lock::{new_handle, try_read, try_write, Handle, ReadGuard, WriteGuard};
use crate::panic_guard::with_unwind_guard;
use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use anyhow::{anyhow, Result};
use core::ffi::{c_char, c_void};
use core::ptr;
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{
    generate_assembly_listing, generate_tabular_assembly_listing, AssemblyListingConfig,
    DeserializationResult, Program,
};
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM};
use regorus::PolicyModule;
use regorus::Value;

/// Wrapper for `regorus::rvm::Program`.
#[derive(Clone)]
pub struct RegorusProgram {
    pub(crate) program: Arc<Program>,
}

/// Wrapper for `regorus::rvm::RegoVM`.
pub struct RegorusRvm {
    vm: Handle<RegoVM>,
}

impl RegorusRvm {
    fn new(vm: RegoVM) -> Self {
        Self { vm: new_handle(vm) }
    }

    fn contention_error() -> anyhow::Error {
        anyhow!("regorus rvm handle is already in use; create a separate VM per thread")
    }

    fn try_write(&self) -> Result<WriteGuard<'_, RegoVM>> {
        try_write(&self.vm).ok_or_else(Self::contention_error)
    }

    fn try_read(&self) -> Result<ReadGuard<'_, RegoVM>> {
        try_read(&self.vm).ok_or_else(Self::contention_error)
    }
}

/// Drop a `RegorusProgram`.
#[no_mangle]
pub extern "C" fn regorus_program_drop(program: *mut RegorusProgram) {
    if let Ok(program) = to_ref(program) {
        unsafe {
            let _ = Box::from_raw(ptr::from_mut(program));
        }
    }
}

/// Drop a `RegorusRvm`.
#[no_mangle]
pub extern "C" fn regorus_rvm_drop(vm: *mut RegorusRvm) {
    if let Ok(vm) = to_ref(vm) {
        unsafe {
            let _ = Box::from_raw(ptr::from_mut(vm));
        }
    }
}

/// Compile a compiled policy into an RVM program.
///
/// * `compiled_policy` - Compiled policy handle
/// * `entry_points` - Array of entry point rule paths
/// * `entry_points_len` - Number of entry points
#[no_mangle]
pub extern "C" fn regorus_program_compile_from_policy(
    compiled_policy: *mut RegorusCompiledPolicy,
    entry_points: *const *const c_char,
    entry_points_len: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<*mut RegorusProgram> {
            if entry_points.is_null() && entry_points_len > 0 {
                return Err(anyhow!("null entry_points pointer"));
            }

            let mut entry_points_vec = Vec::with_capacity(entry_points_len);
            for i in 0..entry_points_len {
                unsafe {
                    let entry_ptr = entry_points.add(i);
                    if entry_ptr.is_null() {
                        return Err(anyhow!("null entry point at index {i}"));
                    }
                    let entry = from_c_str(*entry_ptr)?;
                    entry_points_vec.push(entry);
                }
            }

            let entry_points_ref: Vec<&str> = entry_points_vec.iter().map(|s| s.as_str()).collect();

            let compiled_policy =
                &to_shared_ref(compiled_policy as *const RegorusCompiledPolicy)?.compiled_policy;
            let program = Compiler::compile_from_policy(compiled_policy, &entry_points_ref)?;
            Ok(Box::into_raw(Box::new(RegorusProgram { program })))
        }();

        match output {
            Ok(program) => RegorusResult::ok_pointer(program as *mut c_void),
            Err(err) => RegorusResult::err_with_message(
                RegorusStatus::CompilationFailed,
                format!("RVM compilation failed: {err}"),
            ),
        }
    })
}

/// Compile an RVM program from data/modules and entry points.
///
/// * `data_json` - JSON string containing static data for policy evaluation
/// * `modules` - Array of policy modules to compile
/// * `modules_len` - Number of modules in the array
/// * `entry_points` - Array of entry point rule paths
/// * `entry_points_len` - Number of entry points
#[no_mangle]
pub extern "C" fn regorus_program_compile_from_modules(
    data_json: *const c_char,
    modules: *const RegorusPolicyModule,
    modules_len: usize,
    entry_points: *const *const c_char,
    entry_points_len: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<*mut RegorusProgram> {
            if entry_points_len == 0 {
                return Err(anyhow!("entry_points must contain at least one entry"));
            }

            let data_str = from_c_str(data_json)?;
            let data = Value::from_json_str(&data_str)?;
            let policy_modules = convert_c_modules_to_rust(modules, modules_len)?;

            let entry_points_vec = convert_c_entry_points(entry_points, entry_points_len)?;
            let entry_points_ref: Vec<&str> = entry_points_vec.iter().map(|s| s.as_str()).collect();

            let entry_rule = entry_points_ref
                .first()
                .ok_or_else(|| anyhow!("entry_points must contain at least one entry"))?;

            let compiled_policy = regorus::compile_policy_with_entrypoint(
                data,
                &policy_modules,
                (*entry_rule).into(),
            )?;

            let program = Compiler::compile_from_policy(&compiled_policy, &entry_points_ref)?;
            Ok(Box::into_raw(Box::new(RegorusProgram { program })))
        }();

        match output {
            Ok(program) => RegorusResult::ok_pointer(program as *mut c_void),
            Err(err) => RegorusResult::err_with_message(
                RegorusStatus::CompilationFailed,
                format!("RVM compilation failed: {err}"),
            ),
        }
    })
}

/// Create a new, empty RVM program.
#[no_mangle]
pub extern "C" fn regorus_program_new() -> *mut RegorusProgram {
    let program = Program::new();
    Box::into_raw(Box::new(RegorusProgram {
        program: Arc::new(program),
    }))
}

/// Serialize a program to the binary RVM format.
#[no_mangle]
pub extern "C" fn regorus_program_serialize_binary(program: *mut RegorusProgram) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<*mut RegorusBuffer> {
            let program = &to_shared_ref(program as *const RegorusProgram)?.program;
            let bytes = program.serialize_binary().map_err(|e| anyhow!(e))?;
            Ok(RegorusBuffer::from_vec(bytes))
        }();

        match output {
            Ok(buffer) => RegorusResult::ok_pointer(buffer as *mut c_void),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{err}")),
        }
    })
}

/// Deserialize a program from the binary RVM format.
///
/// Returns a `RegorusProgram` handle and sets `is_partial` to true when the
/// program requires recompilation.
#[no_mangle]
pub extern "C" fn regorus_program_deserialize_binary(
    data: *const u8,
    len: usize,
    is_partial: *mut bool,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<(*mut RegorusProgram, bool)> {
            if data.is_null() {
                if len > 0 {
                    return Err(anyhow!("null data pointer with non-zero length"));
                }
                return Err(anyhow!("null data pointer"));
            }
            let data = unsafe { core::slice::from_raw_parts(data, len) };
            let (program, partial) =
                match Program::deserialize_binary(data).map_err(|e| anyhow!(e))? {
                    DeserializationResult::Complete(program) => (program, false),
                    DeserializationResult::Partial(program) => (program, true),
                };
            Ok((
                Box::into_raw(Box::new(RegorusProgram {
                    program: Arc::new(program),
                })),
                partial,
            ))
        }();

        match output {
            Ok((program, partial)) => {
                if !is_partial.is_null() {
                    unsafe {
                        *is_partial = partial;
                    }
                }
                RegorusResult::ok_pointer(program as *mut c_void)
            }
            Err(err) => {
                RegorusResult::err_with_message(RegorusStatus::InvalidDataFormat, err.to_string())
            }
        }
    })
}

/// Generate a default assembly listing for the program.
#[no_mangle]
pub extern "C" fn regorus_program_generate_listing(program: *mut RegorusProgram) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let program = &to_shared_ref(program as *const RegorusProgram)?.program;
            Ok(generate_assembly_listing(
                program,
                &AssemblyListingConfig::default(),
            ))
        }();

        match output {
            Ok(listing) => RegorusResult::ok_string(listing),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{err}")),
        }
    })
}

/// Generate a tabular assembly listing for the program.
#[no_mangle]
pub extern "C" fn regorus_program_generate_tabular_listing(
    program: *mut RegorusProgram,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let program = &to_shared_ref(program as *const RegorusProgram)?.program;
            Ok(generate_tabular_assembly_listing(
                program,
                &AssemblyListingConfig::default(),
            ))
        }();

        match output {
            Ok(listing) => RegorusResult::ok_string(listing),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{err}")),
        }
    })
}

/// Construct a new RVM instance.
#[no_mangle]
pub extern "C" fn regorus_rvm_new() -> *mut RegorusRvm {
    Box::into_raw(Box::new(RegorusRvm::new(RegoVM::new())))
}

/// Construct a new RVM instance with a compiled policy for default rule evaluation.
#[no_mangle]
pub extern "C" fn regorus_rvm_new_with_policy(
    compiled_policy: *mut RegorusCompiledPolicy,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<*mut RegorusRvm> {
            let policy = to_shared_ref(compiled_policy as *const RegorusCompiledPolicy)?
                .compiled_policy
                .clone();
            Ok(Box::into_raw(Box::new(RegorusRvm::new(
                RegoVM::new_with_policy(policy),
            ))))
        }();

        match output {
            Ok(vm) => RegorusResult::ok_pointer(vm as *mut c_void),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
        }
    })
}

/// Load a program into the RVM.
#[no_mangle]
pub extern "C" fn regorus_rvm_load_program(
    vm: *mut RegorusRvm,
    program: *mut RegorusProgram,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let program = to_shared_ref(program as *const RegorusProgram)?
                .program
                .clone();
            guard.load_program(program);
            Ok(())
        }())
    })
}

/// Set the VM data document from JSON.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_data(vm: *mut RegorusRvm, data: *const c_char) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let data_value = Value::from_json_str(&from_c_str(data)?)?;
            guard.set_data(data_value)?;
            Ok(())
        }())
    })
}

/// Set the VM input document from JSON.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_input(
    vm: *mut RegorusRvm,
    input: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let input_value = Value::from_json_str(&from_c_str(input)?)?;
            guard.set_input(input_value);
            Ok(())
        }())
    })
}

/// Set the VM context document from JSON.
///
/// The context provides host-supplied ambient data (e.g. `resourceGroup()`,
/// `subscription()`) that Azure Policy functions can access via `LoadContext`
/// instructions. This must be called before `regorus_rvm_execute` when
/// evaluating policies that reference context functions.
///
/// # Safety
/// - `vm` must be a valid pointer to a `RegorusRvm` created by `regorus_rvm_new`.
/// - `context_json` must be a valid null-terminated UTF-8 string.
#[cfg(feature = "azure_policy")]
#[no_mangle]
pub extern "C" fn regorus_rvm_set_context(
    vm: *mut RegorusRvm,
    context_json: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let context_value = Value::from_json_str(&from_c_str(context_json)?)?;
            guard.set_context(context_value);
            Ok(())
        }())
    })
}

/// Set the maximum number of instructions that can execute.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_max_instructions(
    vm: *mut RegorusRvm,
    max_instructions: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            guard.set_max_instructions(max_instructions);
            Ok(())
        }())
    })
}

/// Configure strict builtin error behavior.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_strict_builtin_errors(
    vm: *mut RegorusRvm,
    strict: bool,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            guard.set_strict_builtin_errors(strict);
            Ok(())
        }())
    })
}

/// Configure the execution mode (0 = run-to-completion, 1 = suspendable).
#[no_mangle]
pub extern "C" fn regorus_rvm_set_execution_mode(vm: *mut RegorusRvm, mode: u8) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let mode = match mode {
                0 => ExecutionMode::RunToCompletion,
                1 => ExecutionMode::Suspendable,
                _ => return Err(anyhow!("invalid execution mode: {mode}")),
            };
            guard.set_execution_mode(mode);
            Ok(())
        }())
    })
}

/// Enable or disable step mode when running suspendable execution.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_step_mode(vm: *mut RegorusRvm, enabled: bool) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            guard.set_step_mode(enabled);
            Ok(())
        }())
    })
}

/// Configure the per-VM execution timer override.
#[no_mangle]
pub extern "C" fn regorus_rvm_set_execution_timer_config(
    vm: *mut RegorusRvm,
    has_config: bool,
    config: RegorusExecutionTimerConfig,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            if has_config {
                guard.set_execution_timer_config(Some(config.to_execution_timer_config()?));
            } else {
                guard.set_execution_timer_config(None);
            }
            Ok(())
        }())
    })
}

/// Execute the program's main entry point.
#[no_mangle]
pub extern "C" fn regorus_rvm_execute(vm: *mut RegorusRvm) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let result = guard.execute()?;
            result.to_json_str()
        }();

        match output {
            Ok(json) => RegorusResult::ok_string(json),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
        }
    })
}

/// Execute a named entry point.
#[no_mangle]
pub extern "C" fn regorus_rvm_execute_entry_point_by_name(
    vm: *mut RegorusRvm,
    entry_point: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let name = from_c_str(entry_point)?;
            let result = guard.execute_entry_point_by_name(&name)?;
            result.to_json_str()
        }();

        match output {
            Ok(json) => RegorusResult::ok_string(json),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
        }
    })
}

/// Execute an entry point by index.
#[no_mangle]
pub extern "C" fn regorus_rvm_execute_entry_point_by_index(
    vm: *mut RegorusRvm,
    index: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let result = guard.execute_entry_point_by_index(index)?;
            result.to_json_str()
        }();

        match output {
            Ok(json) => RegorusResult::ok_string(json),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
        }
    })
}

/// Resume execution for suspendable runs.
#[no_mangle]
pub extern "C" fn regorus_rvm_resume(
    vm: *mut RegorusRvm,
    resume_value_json: *const c_char,
    has_value: bool,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            let value = if has_value {
                Some(Value::from_json_str(&from_c_str(resume_value_json)?)?)
            } else {
                None
            };
            let result = guard.resume(value)?;
            result.to_json_str()
        }();

        match output {
            Ok(json) => RegorusResult::ok_string(json),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
        }
    })
}

/// Get the current execution state of the VM.
#[no_mangle]
pub extern "C" fn regorus_rvm_get_execution_state(vm: *mut RegorusRvm) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let guard = vm.try_read()?;
            let state: ExecutionState = guard.execution_state().clone();
            Ok(format!("{:?}", state))
        }();

        match output {
            Ok(json) => RegorusResult::ok_string(json),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, err.to_string()),
        }
    })
}

/// Set explanation settings for causality tracking on the RVM.
///
/// * `enabled`: Whether to enable explanation capture.
/// * `value_mode`: 0 = Redacted, 1 = Full.
/// * `condition_mode`: 0 = PrimaryOnly, 1 = AllContributing.
/// * `scope_mode`: 0 = AllEmissions, 1 = SingleEmission, 2 = RuleSummary.
/// * `detail_mode`: 0 = Compact, 1 = Standard, 2 = Full.
/// * `has_emission_index`: Whether `emission_index` should be used.
/// * `emission_index`: 0-based emission index when `scope_mode` is SingleEmission.
/// * `has_emission_value`: Whether `emission_value_json` should be used.
/// * `emission_value_json`: JSON literal or raw string to match against emitted values.
/// * `assume_unknown_input`: Whether to assume unknown input fields exist.
/// * `eval_mode`: 0 = Causality (default), 1 = PartialEval.
/// * `unknowns`: Pointer to array of UTF-8 paths declared as unknown (e.g. "input", "input.deployment").
///   May be null when `unknowns_len` is 0; in that case defaults to `["input"]`.
/// * `unknowns_len`: Number of entries in the `unknowns` array.
#[no_mangle]
#[cfg(feature = "explanations")]
#[allow(clippy::too_many_arguments)]
pub extern "C" fn regorus_rvm_set_explanation_settings(
    vm: *mut RegorusRvm,
    enabled: bool,
    value_mode: u8,
    condition_mode: u8,
    scope_mode: u8,
    detail_mode: u8,
    has_emission_index: bool,
    emission_index: u32,
    has_emission_value: bool,
    emission_value_json: *const c_char,
    assume_unknown_input: bool,
    eval_mode: u8,
    unknowns: *const *const c_char,
    unknowns_len: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_ref(vm)?;
            let mut guard = vm.try_write()?;
            let vm_mode = match value_mode {
                0 => regorus::evaluation_trace::ValueMode::Redacted,
                1 => regorus::evaluation_trace::ValueMode::Full,
                _ => {
                    return Err(anyhow!(
                        "invalid value_mode; expected 0 (Redacted) or 1 (Full)"
                    ))
                }
            };
            let cm = match condition_mode {
                0 => regorus::evaluation_trace::ConditionMode::PrimaryOnly,
                1 => regorus::evaluation_trace::ConditionMode::AllContributing,
                _ => {
                    return Err(anyhow!(
                        "invalid condition_mode; expected 0 (PrimaryOnly) or 1 (AllContributing)"
                    ))
                }
            };
            let scope = match scope_mode {
                0 => regorus::evaluation_trace::ExplanationScope::AllEmissions,
                1 => regorus::evaluation_trace::ExplanationScope::SingleEmission,
                2 => regorus::evaluation_trace::ExplanationScope::RuleSummary,
                _ => {
                    return Err(anyhow!(
                        "invalid scope_mode; expected 0 (AllEmissions), 1 (SingleEmission), or 2 (RuleSummary)"
                    ))
                }
            };
            let detail = match detail_mode {
                0 => regorus::evaluation_trace::ExplanationDetail::Compact,
                1 => regorus::evaluation_trace::ExplanationDetail::Standard,
                2 => regorus::evaluation_trace::ExplanationDetail::Full,
                _ => {
                    return Err(anyhow!(
                        "invalid detail_mode; expected 0 (Compact), 1 (Standard), or 2 (Full)"
                    ))
                }
            };
            let emission_index = if has_emission_index {
                Some(
                    usize::try_from(emission_index)
                        .map_err(|_| anyhow!("emission_index is out of range"))?,
                )
            } else {
                None
            };
            let emission_value = if has_emission_value {
                let raw = from_c_str(emission_value_json)?;
                Some(
                    regorus::Value::from_json_str(&raw)
                        .unwrap_or_else(|_| regorus::Value::from(raw)),
                )
            } else {
                None
            };
            let em = match eval_mode {
                0 => regorus::evaluation_trace::EvaluationMode::Causality,
                1 => regorus::evaluation_trace::EvaluationMode::PartialEval,
                _ => {
                    return Err(anyhow!(
                        "invalid eval_mode; expected 0 (Causality) or 1 (PartialEval)"
                    ))
                }
            };
            let unknown_paths: Vec<String> = if unknowns.is_null() || unknowns_len == 0 {
                alloc::vec![String::from("input")]
            } else {
                convert_c_entry_points(unknowns, unknowns_len)?
            };
            guard.set_explanation_settings(regorus::evaluation_trace::ExplanationSettings {
                enabled,
                value_mode: vm_mode,
                condition_mode: cm,
                scope,
                detail,
                emission_index,
                emission_value,
                assume_unknown_input,
                eval_mode: em,
                unknowns: unknown_paths,
                max_derivations: 1,
            });
            Ok(())
        }())
    })
}

/// Set the maximum number of distinct derivations reported per repeated
/// partial-set value (default 1; 0 is treated as 1).
///
/// `regorus_rvm_set_explanation_settings` resets this to 1, so call this
/// afterwards. With a value above 1, each emission in the causality report
/// carries a `derivations` list.
#[no_mangle]
#[cfg(feature = "explanations")]
pub extern "C" fn regorus_rvm_set_explanation_max_derivations(
    vm: *mut RegorusRvm,
    max_derivations: usize,
) -> RegorusResult {
    with_unwind_guard(|| {
        to_regorus_result(|| -> Result<()> {
            let vm = to_shared_ref(vm as *const RegorusRvm)?;
            let mut guard = vm.try_write()?;
            guard.set_explanation_max_derivations(max_derivations);
            Ok(())
        }())
    })
}

/// Take the causality report from the most recent RVM evaluation as JSON.
#[no_mangle]
#[cfg(feature = "explanations")]
pub extern "C" fn regorus_rvm_take_causality_report(vm: *mut RegorusRvm) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_ref(vm)?;
            let mut guard = vm.try_write()?;
            let report = guard.take_causality_report(regorus::Value::Undefined);
            report.map_err(|e| anyhow!("{e}"))
        }();
        match output {
            Ok(out) => RegorusResult::ok_string(out),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
}

/// Take the causality report from the most recent RVM evaluation as
/// MessagePack bytes (named-field encoding). Returns a `RegorusBuffer*`
/// in the pointer slot; caller must free via `regorus_buffer_drop`.
///
/// Enabled only when the FFI crate is built with `--features causality_msgpack`.
#[no_mangle]
#[cfg(all(feature = "explanations", feature = "causality_msgpack"))]
pub extern "C" fn regorus_rvm_take_causality_report_msgpack(vm: *mut RegorusRvm) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<*mut RegorusBuffer> {
            let vm = to_ref(vm)?;
            let mut guard = vm.try_write()?;
            let bytes = guard
                .take_causality_report_msgpack(regorus::Value::Undefined)
                .map_err(|e| anyhow!("{e}"))?;
            Ok(RegorusBuffer::from_vec(bytes))
        }();
        match output {
            Ok(buffer) => RegorusResult::ok_pointer(buffer as *mut c_void),
            Err(err) => RegorusResult::err_with_message(RegorusStatus::Error, format!("{err}")),
        }
    })
}

/// Take the partial-evaluation result from the most recent RVM evaluation as JSON.
///
/// Returns DNF residual queries with conditions on unknown inputs.
///
/// * `vm`: Pointer to the RVM.
/// * `value_json`: Optional JSON literal/raw string representing the query result value to seed
///   the residual rendering. Pass null to use `Value::Undefined`.
#[no_mangle]
#[cfg(feature = "explanations")]
pub extern "C" fn regorus_rvm_take_partial_eval_result(
    vm: *mut RegorusRvm,
    value_json: *const c_char,
) -> RegorusResult {
    with_unwind_guard(|| {
        let output = || -> Result<String> {
            let vm = to_ref(vm)?;
            let mut guard = vm.try_write()?;
            let value = if value_json.is_null() {
                regorus::Value::Undefined
            } else {
                let raw = from_c_str(value_json)?;
                regorus::Value::from_json_str(&raw).unwrap_or_else(|_| regorus::Value::from(raw))
            };
            guard
                .take_partial_eval_result(value)
                .map_err(|e| anyhow!("{e}"))
        }();
        match output {
            Ok(out) => RegorusResult::ok_string(out),
            Err(e) => to_regorus_result(Err(e)),
        }
    })
}

fn convert_c_entry_points(
    entry_points: *const *const c_char,
    entry_points_len: usize,
) -> Result<Vec<String>> {
    if entry_points.is_null() && entry_points_len > 0 {
        return Err(anyhow!("null entry_points pointer"));
    }

    let mut entry_points_vec = Vec::with_capacity(entry_points_len);
    for i in 0..entry_points_len {
        unsafe {
            let entry_ptr = entry_points.add(i);
            if entry_ptr.is_null() {
                return Err(anyhow!("null entry point at index {i}"));
            }
            let entry = from_c_str(*entry_ptr)?;
            entry_points_vec.push(entry);
        }
    }

    Ok(entry_points_vec)
}

fn convert_c_modules_to_rust(
    modules: *const RegorusPolicyModule,
    modules_len: usize,
) -> Result<Vec<PolicyModule>> {
    if modules.is_null() && modules_len > 0 {
        return Err(anyhow!("null modules pointer"));
    }

    let mut policy_modules = Vec::with_capacity(modules_len);

    for i in 0..modules_len {
        unsafe {
            let module = modules.add(i);
            if module.is_null() {
                return Err(anyhow!("null module at index {i}"));
            }

            let module_ref = &*module;

            let id = from_c_str(module_ref.id)
                .map_err(|e| anyhow!("invalid module id at index {i}: {e}"))?;
            let content = from_c_str(module_ref.content)
                .map_err(|e| anyhow!("invalid module content at index {i}: {e}"))?;

            policy_modules.push(PolicyModule {
                id: id.into(),
                content: content.into(),
            });
        }
    }

    Ok(policy_modules)
}

#[cfg(all(test, feature = "explanations", feature = "std"))]
mod explanation_max_derivations_tests {
    use super::*;
    use crate::common::{regorus_result_drop, RegorusStatus};
    use core::ffi::CStr;
    use std::ffi::CString;

    const POLICY: &str = r#"package bicep
import rego.v1

deny contains "storage must set tls" if {
    some r in input.resources
    not r.tls
}
"#;

    const INPUT: &str = r#"{"resources": {"a": {}, "b": {"tls": "1.2"}, "c": {}}}"#;

    fn new_vm() -> *mut RegorusRvm {
        let mut engine = regorus::Engine::new();
        engine
            .add_policy("rg3.rego".into(), POLICY.into())
            .expect("policy parses");
        let compiled = engine
            .compile_with_entrypoint(&"data.bicep.deny".into())
            .expect("policy compiles");
        let program = regorus::languages::rego::compiler::Compiler::compile_from_policy(
            &compiled,
            &["data.bicep.deny"],
        )
        .expect("program compiles");
        let vm = Box::into_raw(Box::new(RegorusRvm::new(RegoVM::new_with_policy(compiled))));
        let input = CString::new(INPUT).expect("input has no NUL");
        // SAFETY: `vm` was just created from a live Box and is dropped by the caller.
        unsafe {
            (*vm).try_write().expect("vm is free").load_program(program);
        }
        assert_ok(regorus_rvm_set_input(vm, input.as_ptr()));
        vm
    }

    fn assert_ok(result: RegorusResult) {
        assert_eq!(result.status, RegorusStatus::Ok, "expected Ok");
        regorus_result_drop(result);
    }

    fn set_settings(vm: *mut RegorusRvm) {
        assert_ok(regorus_rvm_set_explanation_settings(
            vm,
            true,
            1,
            0,
            0,
            1,
            false,
            0,
            false,
            core::ptr::null(),
            false,
            0,
            core::ptr::null(),
            0,
        ));
    }

    fn evaluate(vm: *mut RegorusRvm) -> serde_json::Value {
        let entry = CString::new("data.bicep.deny").expect("entry has no NUL");
        assert_ok(regorus_rvm_execute_entry_point_by_name(vm, entry.as_ptr()));
        let report = regorus_rvm_take_causality_report(vm);
        assert_eq!(report.status, RegorusStatus::Ok);
        // SAFETY: an Ok string result owns a valid NUL-terminated UTF-8 buffer.
        let text = unsafe { CStr::from_ptr(report.output) }
            .to_str()
            .expect("report is UTF-8")
            .to_string();
        regorus_result_drop(report);
        serde_json::from_str(&text).expect("report is JSON")
    }

    fn derivation_count(report: &serde_json::Value) -> Option<usize> {
        report["rules"][0]["emissions"][0]
            .get("derivations")
            .map(|derivations| derivations.as_array().expect("array").len())
    }

    #[test]
    fn export_enables_derivations_and_settings_reset_it() {
        let vm = new_vm();

        set_settings(vm);
        assert_eq!(derivation_count(&evaluate(vm)), None);

        set_settings(vm);
        assert_ok(regorus_rvm_set_explanation_max_derivations(vm, 5));
        let report = evaluate(vm);
        assert_eq!(derivation_count(&report), Some(2), "{report:#}");
        let subjects: Vec<&str> = report["rules"][0]["emissions"][0]["derivations"]
            .as_array()
            .expect("derivations")
            .iter()
            .filter_map(|derivation| {
                derivation["conditions"]
                    .as_array()?
                    .iter()
                    .filter_map(|condition| condition["left"]["provenance"].as_str())
                    .find(|path| path.ends_with(".tls"))
            })
            .collect();
        assert_eq!(subjects, ["input.resources.a.tls", "input.resources.c.tls"]);

        // `regorus_rvm_set_explanation_settings` replaces every setting.
        assert_ok(regorus_rvm_set_explanation_max_derivations(vm, 5));
        set_settings(vm);
        assert_eq!(derivation_count(&evaluate(vm)), None);

        regorus_rvm_drop(vm);
    }

    #[test]
    fn export_rejects_null_vm() {
        let result = regorus_rvm_set_explanation_max_derivations(core::ptr::null_mut(), 5);
        assert_eq!(result.status, RegorusStatus::Error);
        // SAFETY: an error result owns a valid NUL-terminated message.
        let message = unsafe { CStr::from_ptr(result.error_message) }
            .to_str()
            .expect("message is UTF-8")
            .to_string();
        assert!(message.contains("null pointer"), "{message}");
        regorus_result_drop(result);
    }
}
