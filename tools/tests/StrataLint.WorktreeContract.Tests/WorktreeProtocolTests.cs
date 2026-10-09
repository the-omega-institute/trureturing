using System.Text;
using StrataLint.Runtime;
using StrataLint.Engine;

namespace StrataLint.WorktreeContract.Tests;

public sealed class WorktreeProtocolTests
{
    [Theory]
    [InlineData("recovery_clean_index_with_resolved_conflict_is_preserved")]
    [InlineData("recovery_published_prior_commit_message_is_reconstructable")]
    [InlineData("recovery_local_repository_is_not_a_remote")]
    [InlineData("recovery_checkpoint_protects_input_reads")]
    public void RecoveryQualificationUsesActualIndexAndCommitObjects(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests." + probe], root, TimeSpan.FromSeconds(90), 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("consumer_mirror_uses_real_git_with_stubbed_github")]
    [InlineData("consumer_land_attributes_paths_with_external_checks_stubbed")]
    public void AgentConsumerUsesRealGitAndPreservesIndependentMaterial(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests." + probe], root, TimeSpan.FromSeconds(90), 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void CooperativeProtocolPreservesRealProcessAndGitState()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"), root],
            root, TimeSpan.FromSeconds(180), 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
