// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Evaluation-local identities, not a recorder payload or a report producer.
//! Computed identities say nothing about causal inputs or member provenance.
//! Missing helper, cache, virtual-data and construction-member propagation
//! remains unknown; equal values and allocation addresses never supply identity.
//!
//! Direct input/data paths share identity only within a capture epoch.
//! Evaluation initialization, abort, program/source replacement and recorder
//! replacement invalidate the sidecar. Suspension alone does not. Register
//! windows save and restore origins alongside values, while callee arguments
//! and returned values remain unknown pending helper propagation. Body resets
//! retain exactly the slots the VM retains. Collection mutation currently
//! invalidates the destination rather than claiming complete member tracking.
//! Chained origin work samples the existing timer only while recording.

use alloc::string::ToString as _;
use alloc::vec::Vec;

use crate::explain::{ConcretePath, PathRoot, PathSegment};
use crate::value::Value;

use super::machine::RegoVM;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(super) enum RuntimeOrigin {
    #[default]
    Unknown,
    Source {
        epoch: u64,
        path: ConcretePath,
    },
    Computed {
        epoch: u64,
        instance: u64,
    },
}

impl RuntimeOrigin {
    /// Index only a tracked direct source. A computed collection's member
    /// might itself be a source value; without a member map it is unknown.
    fn indexed(&self, container: &Value, key: &Value) -> Self {
        let Self::Source {
            epoch,
            path: ConcretePath::Captured { root, segments },
        } = self
        else {
            return Self::Unknown;
        };
        if matches!(container[key], Value::Undefined) {
            return Self::Unknown;
        }
        let segment = match (container, key) {
            (Value::Object(_), Value::String(key)) => PathSegment::Key(key.to_string()),
            (Value::Array(_), Value::Number(index)) => match index.as_u64() {
                // Value lookup historically casts to usize. Do not attribute
                // its truncated result to an unaddressable full-u64 slot.
                Some(index) if usize::try_from(index).is_ok() => PathSegment::Index(index),
                _ => return Self::Unknown,
            },
            // Unrepresentable paths cannot be used as shared identities:
            // different non-string keys or set members would collide.
            _ => return Self::Unknown,
        };
        let mut segments = segments.clone();
        segments.push(segment);
        Self::Source {
            epoch: *epoch,
            path: ConcretePath::Captured {
                root: *root,
                segments,
            },
        }
    }
}

#[derive(Debug, Default)]
pub(super) struct RuntimeOrigins {
    epoch: u64,
    exhausted: bool,
    next_instance: u64,
    registers: Vec<RuntimeOrigin>,
    windows: Vec<Vec<RuntimeOrigin>>,
}

impl RuntimeOrigins {
    pub(super) fn reset(&mut self) {
        self.registers.clear();
        self.windows.clear();
        self.next_instance = 0;
        match self.epoch.checked_add(1) {
            Some(epoch) => self.epoch = epoch,
            None => self.exhausted = true,
        }
    }

    pub(super) fn get(&self, register: u8) -> RuntimeOrigin {
        self.registers
            .get(usize::from(register))
            .cloned()
            .unwrap_or_default()
    }

    pub(super) fn set(&mut self, register: u8, origin: RuntimeOrigin) {
        let index = usize::from(register);
        self.registers
            .resize(self.registers.len().max(index + 1), RuntimeOrigin::Unknown);
        self.registers[index] = origin;
    }

    pub(super) fn clear_register(&mut self, register: u8) {
        if let Some(origin) = self.registers.get_mut(usize::from(register)) {
            *origin = RuntimeOrigin::Unknown;
        }
    }

    pub(super) fn resize(&mut self, retained: usize, size: usize) {
        self.registers.resize(retained, RuntimeOrigin::Unknown);
        self.registers.resize(size, RuntimeOrigin::Unknown);
    }

    pub(super) fn enter_window(&mut self) {
        // Arguments deliberately start unknown until helper propagation.
        self.windows.push(core::mem::take(&mut self.registers));
    }

    pub(super) fn leave_window(&mut self) {
        // A recorder installed during suspension has no saved caller origins.
        self.registers = self.windows.pop().unwrap_or_default();
    }

    fn source(&self, root: PathRoot) -> RuntimeOrigin {
        if self.exhausted {
            RuntimeOrigin::Unknown
        } else {
            RuntimeOrigin::Source {
                epoch: self.epoch,
                path: ConcretePath::Captured {
                    root,
                    segments: Vec::new(),
                },
            }
        }
    }

    fn computed(&mut self) -> RuntimeOrigin {
        if self.exhausted {
            return RuntimeOrigin::Unknown;
        }
        let Some(instance) = self.next_instance.checked_add(1) else {
            return RuntimeOrigin::Unknown;
        };
        self.next_instance = instance;
        RuntimeOrigin::Computed {
            epoch: self.epoch,
            instance,
        }
    }
}

impl RegoVM {
    #[cold]
    pub(super) fn explain_source_origin(&mut self, dest: u8, root: PathRoot) {
        let origin = if self
            .registers
            .get(usize::from(dest))
            .is_some_and(|value| !matches!(value, Value::Undefined))
        {
            self.explain.origins.source(root)
        } else {
            RuntimeOrigin::Unknown
        };
        self.explain.origins.set(dest, origin);
    }

    #[cold]
    pub(super) fn explain_computed_origin(&mut self, dest: u8) {
        if self.registers.get(usize::from(dest)).is_some_and(|value| {
            matches!(value, Value::Array(_) | Value::Object(_) | Value::Set(_))
        }) {
            let origin = self.explain.origins.computed();
            self.explain.origins.set(dest, origin);
        }
    }

    pub(super) fn explain_index_origin(&self, container: u8, key: &Value) -> RuntimeOrigin {
        self.registers
            .get(usize::from(container))
            .map(|value| self.explain.origins.get(container).indexed(value, key))
            .unwrap_or_default()
    }

    pub(super) fn explain_chained_origin(
        origin: &RuntimeOrigin,
        container: &Value,
        key: &Value,
    ) -> RuntimeOrigin {
        origin.indexed(container, key)
    }
}

#[cfg(test)]
mod tests;
