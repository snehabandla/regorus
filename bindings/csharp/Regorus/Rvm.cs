// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Execution mode for the RVM runtime.
    /// </summary>
    public enum ExecutionMode : byte
    {
        /// <summary>
        /// Run to completion without yielding.
        /// </summary>
        RunToCompletion = 0,

        /// <summary>
        /// Suspendable execution mode.
        /// </summary>
        Suspendable = 1,
    }

    /// <summary>
    /// Evaluation mode for the explanation/causality system.
    /// </summary>
    public enum EvaluationMode : byte
    {
        /// <summary>
        /// Standard causality reporting (default).
        /// </summary>
        Causality = 0,

        /// <summary>
        /// Partial evaluation - produces residual queries over declared unknowns.
        /// </summary>
        PartialEval = 1,
    }

    /// <summary>
    /// Wrapper for the Regorus RVM runtime.
    /// </summary>
    public unsafe sealed class Rvm : SafeHandleWrapper
    {
        public Rvm()
            : base(RegorusRvmHandle.Create(), nameof(Rvm))
        {
        }

        private Rvm(RegorusRvmHandle handle)
            : base(handle, nameof(Rvm))
        {
        }

        /// <summary>
        /// Create an RVM instance backed by a compiled policy (for default rule evaluation).
        /// </summary>
        public static Rvm CreateWithPolicy(CompiledPolicy policy)
        {
            if (policy is null)
            {
                throw new ArgumentNullException(nameof(policy));
            }

            return policy.UseHandleForInterop(policyPtr =>
            {
                var result = API.regorus_rvm_new_with_policy((RegorusCompiledPolicy*)policyPtr);
                return GetRvmResult(result);
            });
        }

        /// <summary>
        /// Load a program into the VM.
        /// </summary>
        public void LoadProgram(Program program)
        {
            if (program is null)
            {
                throw new ArgumentNullException(nameof(program));
            }

            program.UseHandleForInterop(programPtr =>
            {
                UseHandle(vmPtr =>
                {
                    CheckAndDropResult(API.regorus_rvm_load_program((RegorusRvm*)vmPtr, (RegorusProgram*)programPtr));
                    return 0;
                });
                return 0;
            });
        }

        /// <summary>
        /// Set the data document for the VM.
        /// </summary>
        public void SetDataJson(string dataJson)
        {
            Utf8Marshaller.WithUtf8(dataJson, dataPtr =>
            {
                UseHandle(vmPtr =>
                {
                    CheckAndDropResult(API.regorus_rvm_set_data((RegorusRvm*)vmPtr, (byte*)dataPtr));
                    return 0;
                });
            });
        }

        /// <summary>
        /// Set the input document for the VM.
        /// </summary>
        public void SetInputJson(string inputJson)
        {
            Utf8Marshaller.WithUtf8(inputJson, inputPtr =>
            {
                UseHandle(vmPtr =>
                {
                    CheckAndDropResult(API.regorus_rvm_set_input((RegorusRvm*)vmPtr, (byte*)inputPtr));
                    return 0;
                });
            });
        }

        /// <summary>
        /// Set the context document for the VM.
        /// The context provides host-supplied ambient data (e.g. resourceGroup(),
        /// subscription()) that Azure Policy functions can access via LoadContext
        /// instructions.
        /// </summary>
        public void SetContextJson(string contextJson)
        {
            Utf8Marshaller.WithUtf8(contextJson, contextPtr =>
            {
                UseHandle(vmPtr =>
                {
                    CheckAndDropResult(API.regorus_rvm_set_context((RegorusRvm*)vmPtr, (byte*)contextPtr));
                    return 0;
                });
            });
        }

        /// <summary>
        /// Set the execution mode (0 = run-to-completion, 1 = suspendable).
        /// </summary>
        public void SetExecutionMode(byte mode)
        {
            UseHandle(vmPtr =>
            {
                CheckAndDropResult(API.regorus_rvm_set_execution_mode((RegorusRvm*)vmPtr, mode));
                return 0;
            });
        }

        /// <summary>
        /// Set the execution mode.
        /// </summary>
        public void SetExecutionMode(ExecutionMode mode)
        {
            SetExecutionMode((byte)mode);
        }

        /// <summary>
        /// Set the maximum number of VM instructions a single <see cref="Execute"/> call
        /// is allowed to run before the engine bails with
        /// <c>"Execution stopped: exceeded maximum instruction limit"</c>.
        /// </summary>
        /// <remarks>
        /// Managed wrapper over the existing <c>regorus_rvm_set_max_instructions</c>
        /// entry point. Hosts evaluating large policy sets over many resources can
        /// exceed the default limit, which surfaces as a fail-fast rather than a
        /// result, so the cap needs to be raisable from the binding.
        /// </remarks>
        public void SetMaxInstructions(ulong maxInstructions)
        {
            UseHandle(vmPtr =>
            {
                CheckAndDropResult(API.regorus_rvm_set_max_instructions((RegorusRvm*)vmPtr, (UIntPtr)maxInstructions));
                return 0;
            });
        }

        /// <summary>
        /// Execute the program and return the JSON result.
        /// </summary>
        public string? Execute()
        {
            return UseHandle(vmPtr =>
            {
                return CheckAndDropResult(API.regorus_rvm_execute((RegorusRvm*)vmPtr));
            });
        }

        /// <summary>
        /// Execute a named entry point.
        /// </summary>
        public string? ExecuteEntryPoint(string entryPoint)
        {
            return Utf8Marshaller.WithUtf8(entryPoint, entryPtr =>
            {
                return UseHandle(vmPtr =>
                {
                    return CheckAndDropResult(API.regorus_rvm_execute_entry_point_by_name((RegorusRvm*)vmPtr, (byte*)entryPtr));
                });
            });
        }

        /// <summary>
        /// Execute an entry point by index.
        /// </summary>
        public string? ExecuteEntryPoint(ulong index)
        {
            return UseHandle(vmPtr =>
            {
                return CheckAndDropResult(API.regorus_rvm_execute_entry_point_by_index((RegorusRvm*)vmPtr, (UIntPtr)index));
            });
        }

        /// <summary>
        /// Resume execution with an optional value.
        /// </summary>
        public string? Resume(string? resumeValueJson)
        {
            if (resumeValueJson is null)
            {
                return UseHandle(vmPtr =>
                {
                    return CheckAndDropResult(API.regorus_rvm_resume((RegorusRvm*)vmPtr, null, has_value: false));
                });
            }

            return Utf8Marshaller.WithUtf8(resumeValueJson, valuePtr =>
            {
                return UseHandle(vmPtr =>
                {
                    return CheckAndDropResult(API.regorus_rvm_resume((RegorusRvm*)vmPtr, (byte*)valuePtr, has_value: true));
                });
            });
        }

        /// <summary>
        /// Get the current execution state.
        /// </summary>
        public string? GetExecutionState()
        {
            return UseHandle(vmPtr =>
            {
                return CheckAndDropResult(API.regorus_rvm_get_execution_state((RegorusRvm*)vmPtr));
            });
        }

        /// <summary>
        /// Set explanation settings for causality tracking.
        /// </summary>
        /// <param name="evalMode">Evaluation mode - <see cref="EvaluationMode.Causality"/> for standard causality reporting,
        /// or <see cref="EvaluationMode.PartialEval"/> for partial evaluation against declared unknowns.</param>
        /// <param name="unknowns">Paths declared as unknown inputs (e.g. "input", "input.deployment"). When null or empty, defaults to ["input"].</param>
        public void SetExplanationSettings(bool enabled, ExplanationValueMode valueMode = ExplanationValueMode.Redacted, ExplanationConditionMode conditionMode = ExplanationConditionMode.PrimaryOnly, ExplanationScope scope = ExplanationScope.AllEmissions, ExplanationDetail detail = ExplanationDetail.Standard, uint? emissionIndex = null, string? emissionValueJson = null, bool assumeUnknownInput = false, EvaluationMode evalMode = EvaluationMode.Causality, IReadOnlyList<string>? unknowns = null)
        {
            using var pinnedUnknowns = ModuleMarshalling.PinEntryPoints(unknowns ?? Array.Empty<string>());

            if (emissionValueJson is null)
            {
                UseHandle(vmPtr =>
                {
                    fixed (IntPtr* unknownsPtr = pinnedUnknowns.Buffer)
                    {
                        CheckAndDropResult(API.regorus_rvm_set_explanation_settings((RegorusRvm*)vmPtr, enabled, (byte)valueMode, (byte)conditionMode, (byte)scope, (byte)detail, emissionIndex.HasValue, emissionIndex.GetValueOrDefault(), false, null, assumeUnknownInput, (byte)evalMode, (byte**)unknownsPtr, (UIntPtr)pinnedUnknowns.Length));
                    }
                    return 0;
                });

                return;
            }

            Utf8Marshaller.WithUtf8(emissionValueJson, emissionValuePtr =>
            {
                UseHandle(vmPtr =>
                {
                    fixed (IntPtr* unknownsPtr = pinnedUnknowns.Buffer)
                    {
                        CheckAndDropResult(API.regorus_rvm_set_explanation_settings((RegorusRvm*)vmPtr, enabled, (byte)valueMode, (byte)conditionMode, (byte)scope, (byte)detail, emissionIndex.HasValue, emissionIndex.GetValueOrDefault(), true, (byte*)emissionValuePtr, assumeUnknownInput, (byte)evalMode, (byte**)unknownsPtr, (UIntPtr)pinnedUnknowns.Length));
                    }
                    return 0;
                });
            });
        }

        /// <summary>
        /// Take the causality report from the most recent evaluation as JSON.
        /// </summary>
        public string? TakeCausalityReport()
        {
            return UseHandle(vmPtr =>
            {
                return CheckAndDropResult(API.regorus_rvm_take_causality_report((RegorusRvm*)vmPtr));
            });
        }

        /// <summary>
        /// Take the causality report from the most recent evaluation as MessagePack bytes
        /// (named-field encoding via rmp-serde's <c>to_vec_named</c>). Returns null only on
        /// VM-state failure. The native FFI must be built with the <c>causality_msgpack</c>
        /// cargo feature; calling this against a default-build native DLL will fail with
        /// EntryPointNotFoundException.
        /// </summary>
        public byte[]? TakeCausalityReportMsgpack()
        {
            return UseHandle(vmPtr =>
            {
                return ExtractBuffer(API.regorus_rvm_take_causality_report_msgpack((RegorusRvm*)vmPtr));
            });
        }

        /// <summary>
        /// Take the partial-evaluation result from the most recent evaluation as JSON.
        /// Returns DNF residual queries with conditions on declared unknowns.
        /// </summary>
        /// <param name="valueJson">Optional JSON literal/raw string representing the query result value to seed residual rendering.</param>
        public string? TakePartialEvalResult(string? valueJson = null)
        {
            if (valueJson is null)
            {
                return UseHandle(vmPtr =>
                {
                    return CheckAndDropResult(API.regorus_rvm_take_partial_eval_result((RegorusRvm*)vmPtr, null));
                });
            }

            return Utf8Marshaller.WithUtf8(valueJson, valuePtr =>
            {
                return UseHandle(vmPtr =>
                {
                    return CheckAndDropResult(API.regorus_rvm_take_partial_eval_result((RegorusRvm*)vmPtr, (byte*)valuePtr));
                });
            });
        }

        private static Rvm GetRvmResult(RegorusResult result)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                if (result.data_type != RegorusDataType.Pointer || result.pointer_value == null)
                {
                    throw new Exception("Expected RVM pointer but got different data type");
                }

                var handle = RegorusRvmHandle.FromPointer((IntPtr)result.pointer_value);
                return new Rvm(handle);
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }

        private static string? CheckAndDropResult(RegorusResult result)
        {
            return ResultHelpers.GetStringResult(result);
        }

        /// <summary>
        /// Extract bytes from a RegorusResult that returns a <c>RegorusBuffer*</c>
        /// in <c>pointer_value</c> (the pattern used by <c>regorus_program_serialize_binary</c>
        /// and <c>regorus_rvm_take_causality_report_msgpack</c>). Copies into a managed
        /// <c>byte[]</c> and frees both the buffer and the result.
        /// </summary>
        private static byte[]? ExtractBuffer(RegorusResult result)
        {
            RegorusBuffer* buffer = null;
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                if (result.data_type != RegorusDataType.Pointer || result.pointer_value == null)
                {
                    throw new Exception("Expected buffer pointer but got different data type");
                }

                buffer = (RegorusBuffer*)result.pointer_value;
                var length = checked((int)buffer->len);
                var data = new byte[length];
                if (length > 0)
                {
                    Marshal.Copy((IntPtr)buffer->data, data, 0, length);
                }
                return data;
            }
            finally
            {
                if (buffer != null)
                {
                    API.regorus_buffer_drop(buffer);
                }
                API.regorus_result_drop(result);
            }
        }
    }
}
