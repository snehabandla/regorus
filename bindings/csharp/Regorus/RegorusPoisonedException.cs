// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

namespace Regorus
{
    public sealed class RegorusPoisonedException : InvalidOperationException
    {
        public RegorusPoisonedException(string message)
            : base(message)
        {
        }
    }
}