using System.Text;
using StrataLint.Cli;
using StrataLint.Runtime;
using Xunit.Abstractions;

namespace StrataLint.Tests;

public sealed class ScopedDotnetLaunchTests(ITestOutputHelper output)
{
    [Theory]
    [InlineData("claim", "unset")]
    [InlineData("claim", "unsafe")]
    [InlineData("creation", "unset")]
    [InlineData("creation", "unsafe")]
    [InlineData("recovery", "unset")]
    [InlineData("recovery", "unsafe")]
    [InlineData("build", "unset")]
    [InlineData("build", "unsafe")]
    [InlineData("razor", "unset")]
    [InlineData("razor", "unsafe")]
    public void RealDotnetLaunchReleasesScopesBeforeDescendantCleanup(string mode, string ambient)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "--scoped-dotnet", typeof(WorktreeCommand).Assembly.Location, mode, ambient],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture);
        output.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        output.WriteLine(Encoding.UTF8.GetString(result.StandardError));
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
