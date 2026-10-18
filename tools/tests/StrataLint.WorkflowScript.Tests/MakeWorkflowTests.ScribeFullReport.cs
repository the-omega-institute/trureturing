using System.Text;

namespace StrataLint.WorkflowScript.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void ScribeFullReportValidatesTheCompleteSnapshotWithoutLeanCompilation()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root, "tools/tests/StrataLint.WorkflowScript.Tests/Fixtures/scribe_full_report.py")],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
