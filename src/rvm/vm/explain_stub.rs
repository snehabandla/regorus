// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! No-op path hooks when the `explanations` feature is off (B3 prototype).

use crate::value::Value;

use super::machine::RegoVM;

#[allow(clippy::unused_self, clippy::missing_const_for_fn)]
impl RegoVM {
    #[inline(always)]
    pub(super) fn explain_paths(&self) -> bool {
        false
    }
    #[inline(always)]
    pub(super) fn explain_frames(&self) -> bool {
        false
    }
    #[inline(always)]
    pub(super) fn explain_clear_path(&mut self, _reg: u8) {}
    #[inline(always)]
    pub(super) fn explain_reg_path(&self, _reg: u8) -> u32 {
        u32::MAX
    }
    #[inline(always)]
    pub(super) fn explain_path_root(&mut self, _dest: u8, _data: bool) {}
    #[inline(always)]
    pub(super) fn explain_path_copy(&mut self, _dest: u8, _path: u32) {}
    #[inline(always)]
    pub(super) fn explain_path_child(&mut self, _dest: u8, _parent: u32, _key: &Value) {}
    #[inline(always)]
    pub(super) fn explain_chain_path(&mut self, _params_index: u16, _parent: u32) -> u32 {
        u32::MAX
    }
    #[inline(always)]
    pub(super) fn explain_loop_collection(&mut self, _collection: u8, _value_reg: u8) {}
    #[inline(always)]
    pub(super) fn explain_iteration(&mut self, _value_reg: u8, _key: &Value) {}
    #[inline(always)]
    pub(super) fn explain_push_frame(&mut self, _args: &[u8]) {}
    #[inline(always)]
    pub(super) fn explain_pop_frame(&mut self) {}
    #[inline(always)]
    pub(super) fn explain_body_start(&mut self, _retained: usize) {}
}
