using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string WorkflowScriptProject =
        "tools/tests/StrataLint.WorkflowScript.Tests/StrataLint.WorkflowScript.Tests.csproj";

    [Theory]
    [InlineData("MakeWorkflowTests.cs")]
    [InlineData("MakeWorkflowTests.Dispatch.cs")]
    [InlineData("MakeWorkflowTests.HarnessGateChain.cs")]
    [InlineData("MakeWorkflowTests.PreflightBase.cs")]
    [InlineData("MakeWorkflowTests.ScribeCoarseGate.cs")]
    [InlineData("MakeWorkflowTests.Playbook.cs")]
    [InlineData("MakeWorkflowTests.Remove.cs")]
    [InlineData("CacheMaterialScriptTests.cs")]
    [InlineData("LeanCacheEnsureScriptTests.cs")]
    [InlineData("StrataLint.WorkflowScript.Tests.csproj")]
    public void WorkflowScriptSourcesSelectTheirCompleteProjectWithoutCli(string file)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var plan = Plan($"tools/tests/StrataLint.WorkflowScript.Tests/{file}", "", mode);
            Assert.Equal(WithRepositoryContract(new[] {
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                WorkflowScriptProject,
            }), Strings(plan["execution"]!["tests"]!));
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        }
    }

    [Theory]
    [InlineData("Fixtures/cache_material_contract.py")]
    [InlineData("packages.lock.json")]
    public void WorkflowScriptLocalInputsSelectOnlyTheirCompleteProject(string file)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Equal(WithRepositoryContract(new[] { WorkflowScriptProject }),
                Strings(Plan($"tools/tests/StrataLint.WorkflowScript.Tests/{file}", "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("Makefile")]
    [InlineData("tools/Makefile")]
    [InlineData("tools/lean-inspector/inspect.sh")]
    [InlineData("tools/scripts/clean-lanes.sh")]
    [InlineData("tools/scripts/dotnet-test.sh")]
    [InlineData("tools/scripts/ingest.sh")]
    [InlineData("tools/scripts/local-harness-gate.sh")]
    [InlineData("tools/scripts/preflight.sh")]
    [InlineData("tools/scripts/scribe.sh")]
    [InlineData("tools/scripts/worktree-init.sh")]
    [InlineData("tools/scripts/report/echo-residual-summary.sh")]
    [InlineData("tools/scripts/report/lean-report.sh")]
    [InlineData("tools/scripts/report/report-consumer.sh")]
    [InlineData("tools/scripts/workflow/math-gate.sh")]
    [InlineData("tools/scripts/workflow/playbook-workflows.sh")]
    [InlineData("tools/scripts/workflow/scribe-content-checks.sh")]
    [InlineData("tools/scripts/worktree/lean-cache-ensure.sh")]
    [InlineData("tools/scripts/worktree/warm-donor.sh")]
    [InlineData("tools/scripts/update-renderer-contract.sh")]
    [InlineData("tools/scripts/agent/xi_quantization.py")]
    [InlineData("tools/scripts/agent/test_xi_quantization.py")]
    [InlineData("tools/scripts/worktree/cache_material.py")]
    [InlineData("global.json")]
    [InlineData("tools/TestSupport/StrataLint.ProcessTestSupport/TestProcessRunner.cs")]
    [InlineData("tools/TestSupport/StrataLint.ProcessTestSupport/TestExecutable.cs")]
    [InlineData("tools/TestSupport/StrataLint.TestSupport/TestScratchRoot.cs")]
    [InlineData("tools/StrataLint.Engine/BoundedProcessRunner.cs")]
    [InlineData("tools/StrataLint.Engine/Runtime/ProcessCapture.cs")]
    [InlineData("tools/Trureturing.Truth/TruthExportModel.cs")]
    public void WorkflowScriptRealInputsRetainTheCompleteConsumer(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.Contains(WorkflowScriptProject, Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }

    [Theory]
    [InlineData("tools/scripts/report/report-supervisor.sh")]
    [InlineData("tools/scripts/report/lean-report-input.sh")]
    [InlineData("tools/scripts/lean-report-pair.sh")]
    [InlineData("tools/scripts/pr.sh")]
    [InlineData("tools/scripts/worktree/lean-cache-run.sh")]
    public void WorkflowScriptLiteralOnlyPathsDoNotSelectTheProject(string path)
    {
        foreach (var mode in new[] { "push", "pr" })
            Assert.DoesNotContain(WorkflowScriptProject, Strings(Plan(path, "", mode)["execution"]!["tests"]!));
    }
}
