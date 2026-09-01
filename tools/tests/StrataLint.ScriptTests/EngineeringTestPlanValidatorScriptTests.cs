using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class EngineeringTestPlanValidatorScriptTests
{
    private const string ExpectedHead = "23747a66fdb518fd82dbccc6ca5fca0126d6d33c";
    private const string ExpectedBase = "9727fad6a0fde3f6324b113197dd7a42c64eb3c9";

    [Fact]
    public void ValidSelectedPlanSchemaCompilesAndEmitsSummary()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = Run(ValidPlan);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("selected\t2\t1\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Empty(result.StandardError);
        EngineeringTestReportScriptTests.Verify();
    }

    [Fact]
    public void SchemaMismatchReturnsArtifactFallbackExitCode()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = Run(ValidPlan.Replace("\"version\": 2", "\"version\": 1", StringComparison.Ordinal));

        Assert.Equal(1, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains(
            "ENGINEERING_TEST_PLAN_INVALID",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void WorkflowFallbackModeConvertsSchemaMismatchToFallbackSummary()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = Run(
            ValidPlan.Replace("\"version\": 2", "\"version\": 1", StringComparison.Ordinal),
            artifactFallback: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("invalid\t-1\t0\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Contains(
            "ENGINEERING_TEST_PLAN_INVALID",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void MissingJqReturnsHarnessFailureInsteadOfArtifactFallback()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = Run(ValidPlan, exposeJq: false, artifactFallback: true);

        Assert.Equal(70, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("ENGINEERING_TEST_PLAN_VALIDATOR_FAILURE", error, StringComparison.Ordinal);
        Assert.DoesNotContain("ENGINEERING_TEST_PLAN_INVALID", error, StringComparison.Ordinal);
    }

    private static ProcessOutput Run(
        string artifact,
        bool exposeJq = true,
        bool artifactFallback = false)
    {
        var root = TestRepositoryLayout.FindRoot();
        var script = Path.Combine(
            root,
            "tools",
            "scripts",
            "workflow",
            "engineering-test-plan-validator.sh");
        var scriptArguments = new List<string> { script, "-", ExpectedHead, ExpectedBase };
        if (artifactFallback) scriptArguments.Add("--artifact-fallback");
        var arguments = exposeJq
            ? scriptArguments.ToArray()
            : new[]
                {
                    "-c",
                    "PATH=/path-without-jq exec /bin/bash \"$@\"",
                    "engineering-test-plan-validator-test",
                }
                .Concat(scriptArguments)
                .ToArray();

        return TestProcessRunner.Run(
            "/bin/bash",
            arguments,
            root,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024,
            Encoding.UTF8.GetBytes(artifact));
    }

    private const string ValidPlan = """
        {
          "version": 2,
          "head": "23747a66fdb518fd82dbccc6ca5fca0126d6d33c",
          "base": "9727fad6a0fde3f6324b113197dd7a42c64eb3c9",
          "plan": {
            "kind": "selected",
            "reason": "changed inputs",
            "changed_paths": ["D5/One.lean", "D5/Two.lean"],
            "tests": [
              {
                "assembly": "StrataLint.Tests",
                "project_path": "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
                "id": "StrataLint.Tests.Example",
                "detail": "declared input changed",
                "reason": "declared_input"
              }
            ]
          }
        }
        """;
}
