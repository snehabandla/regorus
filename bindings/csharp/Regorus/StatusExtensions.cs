// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
#if REGORUS_EXPERIMENTAL
using RegorusMemoryBudgetExceededException = Regorus.Experimental.RegorusMemoryBudgetExceededException;
using RegorusMemoryBudgetUnsupportedException = Regorus.Experimental.RegorusMemoryBudgetUnsupportedException;
using RegorusPoisonedException = Regorus.Experimental.RegorusPoisonedException;
#endif

#nullable enable

namespace Regorus.Internal
{
    internal static class StatusExtensions
    {
        internal static Exception CreateException(this RegorusStatus status, string? message)
        {
            var details = string.IsNullOrWhiteSpace(message) ? "Regorus call failed." : message;

            return status switch
            {
                RegorusStatus.Panic => new InvalidOperationException($"Regorus engine panicked: {details}"),
                RegorusStatus.Poisoned => new RegorusPoisonedException($"Regorus engine is poisoned: {details}"),
                RegorusStatus.MemoryBudgetExceeded => new RegorusMemoryBudgetExceededException(details),
                RegorusStatus.MemoryBudgetUnsupportedInSuspendableExecution => new RegorusMemoryBudgetUnsupportedException(details),
                _ => new InvalidOperationException(details),
            };
        }
    }
}
