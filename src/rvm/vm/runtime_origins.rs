// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Evaluation-local identities, not a recorder payload or a report producer.
//! Computed identities say nothing about causal inputs. Constructed members
//! retain only independently captured correspondence, with immutable aliases.
//! Missing helper, cache and virtual-data propagation
//! remains unknown; equal values and allocation addresses never supply identity.
//!
//! Direct input/data paths share identity only within a capture epoch.
//! Evaluation initialization, abort, program/source replacement and recorder
//! replacement invalidate the sidecar. Suspension alone does not. Register
//! windows save and restore origins alongside values, while callee arguments
//! and returned values remain unknown pending helper propagation. Body resets
//! retain exactly the slots the VM retains. Unknown members stay unknown;
//! duplicate set contributions with different origins cannot select a source.
//! Chained origin work samples the existing timer only while recording.

use alloc::collections::BTreeMap;
use alloc::string::ToString as _;
use alloc::vec::Vec;

use crate::explain::{ConcretePath, PathRoot, PathSegment};
use crate::value::Value;
use crate::Rc;

use super::errors::Result;
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
    /// An immutable snapshot; fallback covers only untouched members.
    Collection {
        epoch: u64,
        instance: u64,
        members: Rc<BTreeMap<Value, RuntimeOrigin>>,
        fallback: Rc<RuntimeOrigin>,
    },
}

pub(super) struct MemberWrite {
    previous: RuntimeOrigin,
    key: Option<Value>,
    member: RuntimeOrigin,
    duplicate: bool,
}

impl RuntimeOrigin {
    fn indexed(&self, container: &Value, key: &Value) -> Self {
        if matches!(container[key], Value::Undefined)
            || matches!((container, key), (Value::Array(_), Value::Number(index))
                if index.as_u64().is_some_and(|index| usize::try_from(index).is_err()))
        {
            return Self::Unknown;
        }
        if let Self::Collection {
            members, fallback, ..
        } = self
        {
            return members
                .get(key)
                .cloned()
                .unwrap_or_else(|| fallback.indexed(container, key));
        }
        let &Self::Source {
            epoch,
            path: ConcretePath::Captured { root, ref segments },
        } = self
        else {
            return Self::Unknown;
        };
        let segment = match *key {
            Value::String(ref key) if matches!(container, &Value::Object(_)) => {
                PathSegment::Key(key.to_string())
            }
            Value::Number(ref index) if matches!(container, &Value::Array(_)) => {
                match index.as_u64() {
                    // Value lookup historically casts to usize. Do not attribute
                    // its truncated result to an unaddressable full-u64 slot.
                    Some(index) if usize::try_from(index).is_ok() => PathSegment::Index(index),
                    _ => return Self::Unknown,
                }
            }
            // Unrepresentable paths cannot be used as shared identities:
            // different non-string keys or set members would collide.
            _ => return Self::Unknown,
        };
        let mut segments = segments.clone();
        segments.push(segment);
        Self::Source {
            epoch,
            path: ConcretePath::Captured { root, segments },
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
        if let Some(slot) = self.registers.get_mut(index) {
            *slot = origin;
        }
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

    const fn source(&self, root: PathRoot) -> RuntimeOrigin {
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

    const fn computed(&mut self) -> RuntimeOrigin {
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
    fn explain_member_origin(
        &mut self,
        previous: RuntimeOrigin,
        key: Value,
        member: RuntimeOrigin,
        duplicate: bool,
    ) -> Result<RuntimeOrigin> {
        let RuntimeOrigin::Computed { epoch, instance } = self.explain.origins.computed() else {
            return Ok(RuntimeOrigin::Unknown);
        };
        let (mut members, fallback) = match previous {
            RuntimeOrigin::Collection {
                members, fallback, ..
            } => (members, fallback),
            origin => (Rc::new(BTreeMap::new()), Rc::new(origin)),
        };
        // Copy-on-write snapshots can copy every retained entry when aliased.
        self.execution_timer_tick(
            u32::try_from(members.len().saturating_add(1)).unwrap_or(u32::MAX),
        )?;
        self.memory_check()?;
        let member = if duplicate && members.get(&key) != Some(&member) {
            RuntimeOrigin::Unknown
        } else {
            member
        };
        Rc::make_mut(&mut members).insert(key, member);
        self.memory_check()?;
        Ok(RuntimeOrigin::Collection {
            epoch,
            instance,
            members,
            fallback,
        })
    }

    #[cold]
    pub(super) fn explain_collection_write(
        &self,
        container: u8,
        value: u8,
        key: Value,
        set: bool,
    ) -> Result<MemberWrite> {
        let previous = self.explain.origins.get(container);
        let skipped = set && matches!(self.get_register(value)?, Value::Undefined);
        let duplicate = set && !matches!(self.get_register(container)?[&key], Value::Undefined);
        let member = self.explain.origins.get(value);
        Ok(MemberWrite {
            previous,
            key: (!skipped).then_some(key),
            member,
            duplicate,
        })
    }

    #[cold]
    pub(super) fn explain_finish_collection_write(
        &mut self,
        dest: u8,
        write: MemberWrite,
    ) -> Result<()> {
        let origin = match write.key {
            Some(key) => self.explain_member_origin(
                write.previous, key, write.member, write.duplicate,
            )?,
            None => write.previous,
        };
        self.explain.origins.set(dest, origin);
        Ok(())
    }

    #[cold]
    pub(super) fn explain_constructor_origin(
        &mut self,
        fields: &[(Value, u8)],
        set: bool,
    ) -> Result<RuntimeOrigin> {
        let mut origin = self.explain.origins.computed();
        for (key, register) in fields {
            let duplicate = set && matches!(&origin,
                RuntimeOrigin::Collection { members, .. } if members.contains_key(key));
            origin = self.explain_member_origin(
                origin,
                key.clone(),
                self.explain.origins.get(*register),
                duplicate,
            )?;
        }
        Ok(origin)
    }

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
