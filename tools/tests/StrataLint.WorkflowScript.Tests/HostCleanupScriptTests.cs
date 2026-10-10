using System.Text;
using StrataLint.Engine;

namespace StrataLint.WorkflowScript.Tests;

public sealed class HostCleanupScriptTests
{
    [Fact]
    public void RunLocalCleanupUsesCommonWorktreePreservationQualification()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests.runlocal_consumer"], root, TimeSpan.FromSeconds(90), 1024 * 1024,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void CleanupAndWorktreePreflightMeetTheirBehaviorContract()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run(
            "python3",
            ["-B", Path.Combine(root, "tools/tests/StrataLint.WorkflowScript.Tests/Fixtures/host_cleanup_tests.py"),
                Path.Combine(root, "tools/scripts/host-cleanup.py")],
            root,
            TimeSpan.FromSeconds(120),
            1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
