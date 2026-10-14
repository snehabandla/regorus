// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

#if REGORUS_EXPERIMENTAL
namespace Regorus.Experimental
#else
namespace Regorus
#endif
{
    public sealed class RegorusPoisonedException : InvalidOperationException
    {
        public RegorusPoisonedException(string message)
            : base(message)
        {
        }
    }
}
