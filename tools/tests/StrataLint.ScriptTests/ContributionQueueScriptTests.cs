using System.Text;

namespace StrataLint.Tests;

public sealed class ContributionQueueScriptTests
{
    [Fact]
    public void ReadOnlyQueueHonorsOwnerAndCiBoundaries()
    {
        var root = TestRepositoryLayout.FindRoot();
        using var directory = new TemporaryDirectory();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.ScriptTests/Fixtures/contribution_queue_contract.py")],
            directory.Path, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
