using StrataLint.Engine;

namespace StrataLint.LeanReportScript.Tests;

public sealed class LeanInspectorScriptTests
{
    [Fact]
    public void InspectorRecordsInvocationLocalReportAndProgramBuildWork()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B",
            Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/build_work_contract.py")], root,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.True(result.ExitCode == 0, System.Text.Encoding.UTF8.GetString(result.StandardOutput) +
            System.Text.Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("--output")]
    [InlineData("--repository")]
    [InlineData("--unknown")]
    public void InvalidInvocationNeverPublishes(string argument)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("bash", [Path.Combine(root, "tools/lean-inspector/inspect.sh"), argument], root,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(2, result.ExitCode);
    }
}
