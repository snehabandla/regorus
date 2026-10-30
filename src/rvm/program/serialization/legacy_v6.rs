// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Decoder for the core section of version 6 binary programs.
//!
//! Postcard is not self-describing, so the version 6 layout is mirrored here.
//! It only lacks the `ObjectDeepSet` parameter table, which version 7 appended
//! to [`InstructionData`]; opcode numbers are unchanged because
//! `Instruction::ObjectDeepSet` is the last variant.

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use serde::Deserialize;

use super::super::metadata::ProgramMetadata;
use super::super::types::{BuiltinInfo, RuleInfo, SpanInfo};
use super::Program;
use crate::rvm::instructions::{
    ArrayCreateParams, BuiltinCallParams, ChainedIndexParams, ComprehensionBeginParams,
    FunctionCallParams, InstructionData, LoopStartParams, ObjectCreateParams, SetCreateParams,
    VirtualDataDocumentLookupParams,
};
use crate::rvm::Instruction;

/// Version 6 `InstructionData` (field order must match exactly).
#[derive(Deserialize)]
struct InstructionDataV6 {
    loop_params: Vec<LoopStartParams>,
    builtin_call_params: Vec<BuiltinCallParams>,
    function_call_params: Vec<FunctionCallParams>,
    object_create_params: Vec<ObjectCreateParams>,
    array_create_params: Vec<ArrayCreateParams>,
    set_create_params: Vec<SetCreateParams>,
    virtual_data_document_lookup_params: Vec<VirtualDataDocumentLookupParams>,
    chained_index_params: Vec<ChainedIndexParams>,
    comprehension_begin_params: Vec<ComprehensionBeginParams>,
}

/// Serialized fields of a version 6 `Program` (field order must match exactly;
/// fields skipped by serde are not encoded).
#[derive(Deserialize)]
pub(super) struct ProgramV6 {
    instructions: Vec<Instruction>,
    instruction_data: InstructionDataV6,
    builtin_info_table: Vec<BuiltinInfo>,
    rule_infos: Vec<RuleInfo>,
    instruction_spans: Vec<Option<SpanInfo>>,
    main_entry_point: u32,
    max_rule_window_size: u8,
    dispatch_window_size: u8,
    metadata: ProgramMetadata,
    needs_runtime_recursion_check: bool,
    has_host_await: bool,
    needs_recompilation: bool,
}

impl ProgramV6 {
    /// Convert to the current layout, rejecting opcodes version 6 never had.
    pub(super) fn into_program(self) -> Result<Program, String> {
        if self
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, Instruction::ObjectDeepSet { .. }))
        {
            return Err("Invalid version 6 program: ObjectDeepSet requires version 7".to_string());
        }
        let data = self.instruction_data;
        let mut program = Program::new();
        program.instructions = self.instructions;
        program.instruction_data = InstructionData {
            loop_params: data.loop_params,
            builtin_call_params: data.builtin_call_params,
            function_call_params: data.function_call_params,
            object_create_params: data.object_create_params,
            array_create_params: data.array_create_params,
            set_create_params: data.set_create_params,
            virtual_data_document_lookup_params: data.virtual_data_document_lookup_params,
            chained_index_params: data.chained_index_params,
            comprehension_begin_params: data.comprehension_begin_params,
            object_deep_set_params: Vec::new(),
        };
        program.builtin_info_table = self.builtin_info_table;
        program.rule_infos = self.rule_infos;
        program.instruction_spans = self.instruction_spans;
        program.main_entry_point = self.main_entry_point;
        program.max_rule_window_size = self.max_rule_window_size;
        program.dispatch_window_size = self.dispatch_window_size;
        program.metadata = self.metadata;
        program.needs_runtime_recursion_check = self.needs_runtime_recursion_check;
        program.has_host_await = self.has_host_await;
        program.needs_recompilation = self.needs_recompilation;
        Ok(program)
    }
}
