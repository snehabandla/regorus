// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Text.Json;
using System.Text.Json.Nodes;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Regorus.Experimental;

namespace Regorus.Experimental.Tests;

[TestClass]
public sealed class AssumptionTests
{
    private const string SimplePolicy = """
        package test
        default allow = false
        allow if { input.role == "admin" }
        """;

    private const string AliasPolicy = """
        package test
        default allow = false

        role := input.identity.role
        expected_role := "release-admin"

        allow if {
            er := expected_role
            role == er
        }
        """;

    [TestMethod]
    public void Rvm_assumptions_populated_for_simple_policy()
    {
        using var engine = new Engine();
        engine.AddPolicy("test.rego", SimplePolicy);

        var entryPoints = new[] { "data.test.allow" };
        using var program = Program.CompileFromEngine(engine, entryPoints);

        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetExplanationSettings(
            enabled: true,
            valueMode: ExplanationValueMode.Full,
            conditionMode: ExplanationConditionMode.AllContributing,
            detail: ExplanationDetail.Full,
            assumeUnknownInput: true);

        vm.SetInputJson("{}");
        var result = vm.ExecuteEntryPoint("data.test.allow");
        Assert.AreEqual("true", result);

        var reportJson = vm.TakeCausalityReport();
        Assert.IsNotNull(reportJson, "RVM causality report should not be null");

        var report = JsonNode.Parse(reportJson!)!;

        var assumptions = report["assumptions"]?.AsArray();
        Assert.IsNotNull(assumptions, "assumptions should be present");
        Assert.IsTrue(assumptions!.Count > 0, "assumptions should not be empty");

        var first = assumptions[0]!;
        Assert.AreEqual("input.role", (string?)first["input_path"]);
        Assert.AreEqual("==", (string?)first["operator"]);
        Assert.AreEqual("admin", (string?)first["assumed_value"]);
    }

    [TestMethod]
    public void Rvm_assumptions_follow_aliases()
    {
        using var engine = new Engine();
        engine.AddPolicy("test.rego", AliasPolicy);

        var entryPoints = new[] { "data.test.allow" };
        using var program = Program.CompileFromEngine(engine, entryPoints);

        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetExplanationSettings(
            enabled: true,
            valueMode: ExplanationValueMode.Full,
            conditionMode: ExplanationConditionMode.AllContributing,
            detail: ExplanationDetail.Full,
            assumeUnknownInput: true);

        vm.SetInputJson("""{"identity": {"name": "alex"}}""");
        var result = vm.ExecuteEntryPoint("data.test.allow");
        Assert.AreEqual("true", result);

        var reportJson = vm.TakeCausalityReport();
        Assert.IsNotNull(reportJson);

        var report = JsonNode.Parse(reportJson!)!;
        var assumptions = report["assumptions"]?.AsArray();
        Assert.IsNotNull(assumptions);
        Assert.IsTrue(assumptions!.Count > 0, "assumptions should not be empty");

        Assert.AreEqual("input.identity.role", (string?)assumptions[0]!["input_path"]);
        Assert.AreEqual("==", (string?)assumptions[0]!["operator"]);
        Assert.AreEqual("release-admin", (string?)assumptions[0]!["assumed_value"]);
    }

    [TestMethod]
    public void Rvm_loop_witness_populated()
    {
        const string loopPolicy = """
            package test
            default allow = false
            allow if {
                n := input.values[_]
                n > 1
                n < 3
            }
            """;

        using var engine = new Engine();
        engine.AddPolicy("test.rego", loopPolicy);

        var entryPoints = new[] { "data.test.allow" };
        using var program = Program.CompileFromEngine(engine, entryPoints);

        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetExplanationSettings(
            enabled: true,
            valueMode: ExplanationValueMode.Full,
            conditionMode: ExplanationConditionMode.AllContributing,
            detail: ExplanationDetail.Standard);

        vm.SetInputJson("""{"values": [0, 2, 4]}""");
        var result = vm.ExecuteEntryPoint("data.test.allow");
        Assert.AreEqual("true", result);

        var reportJson = vm.TakeCausalityReport();
        Assert.IsNotNull(reportJson);

        var report = JsonNode.Parse(reportJson!)!;
        var rules = report["rules"]?.AsArray();
        Assert.IsNotNull(rules);
        Assert.IsTrue(rules!.Count > 0);

        // Find a condition with a witness
        bool foundWitness = false;
        foreach (var rule in rules)
        {
            var definitions = rule?["definitions"]?.AsArray();
            if (definitions == null) continue;
            foreach (var def in definitions)
            {
                var conditions = def?["conditions"]?.AsArray();
                if (conditions == null) continue;
                foreach (var cond in conditions)
                {
                    var witness = cond?["witness"];
                    if (witness != null && witness.GetValueKind() == JsonValueKind.Object)
                    {
                        foundWitness = true;
                        Assert.IsNotNull(witness["total_iterations"],
                            "witness should have total_iterations");
                        Assert.IsNotNull(witness["success_count"],
                            "witness should have success_count");
                        var total = (int?)witness["total_iterations"];
                        Assert.IsTrue(total > 0,
                            $"total_iterations should be > 0, got {total}");
                    }
                }
            }
        }

        Assert.IsTrue(foundWitness,
            $"expected at least one condition with a loop witness.\nReport:\n{reportJson}");
    }

    [TestMethod]
    public void Rvm_partial_eval_uses_explicit_unknown_paths()
    {
        using var engine = new Engine();
        engine.AddPolicy("test.rego", SimplePolicy);

        using var program = Program.CompileFromEngine(engine, new[] { "data.test.allow" });
        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetExplanationSettings(
            enabled: true,
            valueMode: ExplanationValueMode.Full,
            conditionMode: ExplanationConditionMode.AllContributing,
            detail: ExplanationDetail.Full,
            assumeUnknownInput: true,
            evaluationMode: EvaluationMode.PartialEval,
            unknowns: new[] { "input.role" });

        vm.SetInputJson("{}");
        var result = vm.ExecuteEntryPoint("data.test.allow");
        Assert.AreEqual("true", result);

        var reportJson = vm.TakePartialEvalResult(result);
        Assert.IsNotNull(reportJson);
        var report = JsonNode.Parse(reportJson!)!;
        Assert.AreEqual(true, (bool?)report["result"]);

        var residualQueries = report["residual_queries"]?.AsArray();
        Assert.IsNotNull(residualQueries);
        Assert.IsTrue(residualQueries!.Count > 0);
        var selectedCondition = residualQueries[0]?[0];
        Assert.AreEqual("input.role", (string?)selectedCondition?["input_path"]);
        Assert.AreEqual("==", (string?)selectedCondition?["operator"]);
        Assert.AreEqual("admin", (string?)selectedCondition?["value"]);

        using var excludedVm = new Rvm();
        excludedVm.LoadProgram(program);
        excludedVm.SetExplanationSettings(
            enabled: true,
            assumeUnknownInput: true,
            evaluationMode: EvaluationMode.PartialEval,
            unknowns: new[] { "input.other" });
        excludedVm.SetInputJson("{}");
        Assert.AreEqual("false", excludedVm.ExecuteEntryPoint("data.test.allow"));
        var excludedReport = JsonNode.Parse(excludedVm.TakePartialEvalResult("false")!)!;
        Assert.AreEqual(0, excludedReport["residual_queries"]?.AsArray().Count);

        using var emptyVm = new Rvm();
        emptyVm.LoadProgram(program);
        emptyVm.SetExplanationSettings(
            enabled: true,
            assumeUnknownInput: true,
            evaluationMode: EvaluationMode.PartialEval,
            unknowns: Array.Empty<string>());
        emptyVm.SetInputJson("{}");
        Assert.AreEqual("false", emptyVm.ExecuteEntryPoint("data.test.allow"));
        var emptyReport = JsonNode.Parse(emptyVm.TakePartialEvalResult("false")!)!;
        Assert.AreEqual(0, emptyReport["residual_queries"]?.AsArray().Count);

        using var defaultVm = new Rvm();
        defaultVm.LoadProgram(program);
        defaultVm.SetExplanationSettings(
            enabled: true,
            assumeUnknownInput: true,
            evaluationMode: EvaluationMode.PartialEval);
        defaultVm.SetInputJson("{}");
        Assert.AreEqual("true", defaultVm.ExecuteEntryPoint("data.test.allow"));
        var defaultReport = JsonNode.Parse(defaultVm.TakePartialEvalResult("true")!)!;
        Assert.AreEqual(
            "input.role",
            (string?)defaultReport["residual_queries"]?[0]?[0]?["input_path"]);
    }

    [TestMethod]
    public void Rvm_explanation_settings_reject_invalid_evaluation_mode()
    {
        using var vm = new Rvm();

        var exception = Assert.ThrowsException<InvalidOperationException>(() =>
            vm.SetExplanationSettings(
                enabled: true,
                evaluationMode: (EvaluationMode)byte.MaxValue));

        StringAssert.Contains(exception.Message, "invalid eval_mode");
    }

    [TestMethod]
    public void Rvm_explanation_settings_reject_embedded_nul_in_unknown_path()
    {
        using var vm = new Rvm();

        Assert.ThrowsException<ArgumentException>(() =>
            vm.SetExplanationSettings(
                enabled: true,
                evaluationMode: EvaluationMode.PartialEval,
                unknowns: new[] { "input\0.role" }));
    }

    [TestMethod]
    public void Rvm_partial_eval_rejects_invalid_result_without_consuming_trace()
    {
        using var engine = new Engine();
        engine.AddPolicy("test.rego", SimplePolicy);

        using var program = Program.CompileFromEngine(engine, new[] { "data.test.allow" });
        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetExplanationSettings(
            enabled: true,
            assumeUnknownInput: true,
            evaluationMode: EvaluationMode.PartialEval,
            unknowns: new[] { "input.role" });
        vm.SetInputJson("{}");
        Assert.AreEqual("true", vm.ExecuteEntryPoint("data.test.allow"));

        Assert.ThrowsException<ArgumentException>(() => vm.TakePartialEvalResult("true\0garbage"));
        Assert.ThrowsException<InvalidOperationException>(() => vm.TakePartialEvalResult("tru"));

        var report = JsonNode.Parse(vm.TakePartialEvalResult("true")!)!;
        Assert.IsTrue(report["residual_queries"]?.AsArray().Count > 0);
    }
}
