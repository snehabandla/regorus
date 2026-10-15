#if REGORUS_FFI_TEST_HOOKS
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Regorus.Internal;

namespace Regorus.Tests;

[TestClass]
[DoNotParallelize]
public sealed class PanicGuardTests
{
    [TestInitialize]
    public void Initialize()
    {
        PanicGuardTestHooks.ResetPoison();
    }

    [TestCleanup]
    public void Cleanup()
    {
        PanicGuardTestHooks.ResetPoison();
    }

    [TestMethod]
    public void Panic_produces_invalid_operation_exception()
    {
        var panic = Assert.ThrowsException<InvalidOperationException>(PanicGuardTestHooks.TriggerPanic);
        Assert.IsFalse(panic is RegorusPoisonedException);
        StringAssert.Contains(panic.Message, "panicked", "panic message should capture payload");
    }

    [TestMethod]
    public void Poison_flag_blocks_subsequent_calls()
    {
        _ = Assert.ThrowsException<InvalidOperationException>(PanicGuardTestHooks.TriggerPanic);
        var poisoned = Assert.ThrowsException<RegorusPoisonedException>(PanicGuardTestHooks.TriggerPanic);
        Assert.IsInstanceOfType<InvalidOperationException>(poisoned);
        StringAssert.Contains(poisoned.Message, "poisoned", "poisoned message should explain guard state");
    }

    [TestMethod]
    public void Reset_restores_normal_evaluation()
    {
        _ = Assert.ThrowsException<InvalidOperationException>(PanicGuardTestHooks.TriggerPanic);
        PanicGuardTestHooks.ResetPoison();

        using var engine = new Engine();
        engine.AddPolicy("test.rego", "package test\nmessage := `healthy`");
        Assert.AreEqual("\"healthy\"", engine.EvalRule("data.test.message"));
    }
}

#endif
