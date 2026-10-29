// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod arithmetic;
mod comprehension;
mod context;
mod dispatch;
mod errors;
mod execution;
mod execution_model;
#[cfg(feature = "explanations")]
mod explain_trace;
mod functions;
mod loops;
mod machine;
mod rules;
mod state;
mod virtual_data;

pub use context::{CallRuleContext, IterationState, LoopContext};
pub use errors::{Result, VmError};
pub use execution_model::{ExecutionMode, ExecutionState, SuspendReason};
#[cfg(feature = "explanations")]
pub use explain_trace::{
    ExplainCapture, ExplainDetail, ExplainOutput, ExplainProtoError, IterationRow, SiteStatic,
    TraceBudget, TraceLimit, TraceTruncation,
};
pub use machine::RegoVM;
