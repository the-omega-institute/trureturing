using System.Text;

namespace StrataLint.Tests;

public sealed class LeanReportSelectionTests
{
    [Theory]
    [InlineData("registration_failures")]
    [InlineData("glob_semantics")]
    [InlineData("cohort_changes")]
    [InlineData("source_and_policy_identity")]
    [InlineData("failure_before_build")]
    [InlineData("delta_records")]
    [InlineData("planner_changes")]
    [InlineData("entrypoint_failures")]
    public void RegisteredSelectionContract(string scenario)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root, "tools/tests/StrataLint.ScriptTests/lean_report_selection_fixture.py"),
                root, temporary.Path, scenario], temporary.Path,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }
}
