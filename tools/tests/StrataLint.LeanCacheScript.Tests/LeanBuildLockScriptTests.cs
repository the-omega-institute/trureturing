using System.Text;

namespace StrataLint.LeanCacheScript.Tests;

public sealed class LeanBuildLockScriptTests
{
    [Theory]
    [InlineData("test_main_and_linked_worktrees_wait_across_all_build_phases")]
    [InlineData("test_failed_build_preserves_status_and_releases_waiter")]
    [InlineData("test_terminated_build_releases_waiter")]
    [InlineData("test_cancelled_waiter_leaves_holder_and_next_waiter_intact")]
    [InlineData("test_unrelated_repositories_build_independently")]
    [InlineData("test_missing_git_identity_fails_before_producer")]
    [InlineData("test_skip_lock_runs_while_another_build_holds_lock_without_releasing_it")]
    [InlineData("test_skip_lock_does_not_block_other_builds_during_any_package_phase")]
    public void BuildExclusionSpansWorktreesAndPreservesFailureAndCancellation(string test)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.LeanCacheScript.Tests/Fixtures/lean_build_lock_contract.py"),
                "LeanBuildLockTests." + test],
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
