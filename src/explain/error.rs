// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::vm::VmError;
use alloc::string::String;
use thiserror::Error;

/// Errors produced while capturing or reporting explanations.
#[derive(Error, Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum ExplainError {
    /// A report was requested, but explanation capture was not enabled for
    /// the evaluation.
    #[error("explanations were not enabled for this evaluation")]
    NotEnabled,

    /// [`ExplanationScope::SingleEmission`](super::ExplanationScope::SingleEmission)
    /// selected an emission that the rule did not produce.
    #[error("emission index {index} is out of range for rule `{rule}` ({available} emissions)")]
    EmissionIndexOutOfRange {
        /// Fully qualified rule name.
        rule: String,
        /// The requested emission index.
        index: usize,
        /// Number of emissions the rule produced.
        available: usize,
    },

    /// A declared unknown path is invalid, for example because it overlaps
    /// another one.
    #[error("invalid unknown path `{path}`: {reason}")]
    InvalidUnknownPath {
        /// The path, rendered as Rego.
        path: String,
        /// Why it is invalid.
        reason: String,
    },

    /// A value was supplied at or under a declared unknown path.
    #[error("a value is supplied for unknown path `{path}`")]
    UnknownValueSupplied {
        /// The path, rendered as Rego.
        path: String,
    },

    /// Partial evaluation does not support suspendable execution yet.
    #[error("partial evaluation does not support suspendable execution")]
    PartialEvalSuspendable,

    /// The evaluation itself failed.
    #[error(transparent)]
    Vm(#[from] VmError),
}
