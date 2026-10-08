using System.Text;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    private const string InitializationLock = "worktree-init:01234567890123456789012345678901";

    [Fact]
    public void LockedStagedOnlyMaterialSurvivesHeadMatchingCheckout()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/staged-only");
        File.AppendAllText(Path.Combine(lane, "README.md"), "unique staged work\n");
        CleanLanesFixture.Git(lane, "add", "README.md");
        CleanLanesFixture.Git(lane, "restore", "--source=HEAD", "--worktree", "README.md");
        Assert.NotEmpty(CleanLanesFixture.Git(lane, "diff", "--cached", "HEAD"));
        Assert.Empty(CleanLanesFixture.Git(lane, "diff", "HEAD", "--", "README.md"));
        AssertLockedContentRetained(fixture, lane, "locked_content");
    }

    [Fact]
    public void LockedUnmergedIndexSurvives()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/unmerged-index");
        var blob = CleanLanesFixture.Git(lane, "rev-parse", "HEAD:README.md").Trim();
        var input = $"0 {new string('0', blob.Length)}\tREADME.md\n100644 {blob} 1\tREADME.md\n"
            + $"100644 {blob} 2\tREADME.md\n100644 {blob} 3\tREADME.md\n";
        var update = TestProcessRunner.Run("git", ["update-index", "--index-info"], lane,
            TestBudgets.ScriptProcessHangGuard, 4096, Encoding.UTF8.GetBytes(input));
        Assert.Equal(0, update.ExitCode);
        Assert.NotEmpty(CleanLanesFixture.Git(lane, "ls-files", "--unmerged"));
        AssertLockedContentRetained(fixture, lane, "locked_content");
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MissingIndexNewOrModifiedMaterialSurvives(bool newFile)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/partial-content");
        fixture.RemoveWorktreeIndex(lane);
        File.WriteAllText(Path.Combine(lane, newFile ? "new.txt" : "README.md"), "unique material\n");
        AssertLockedContentRetained(fixture, lane, "locked_content");
    }

    [Fact]
    public void UnreadableIndexIsRetainedAsUnverifiable()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/corrupt-index");
        File.WriteAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "index"), "invalid index");
        AssertLockedContentRetained(fixture, lane, "locked_evidence");
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CleanBehindButDivergentLockedTipIsRetained(bool detached)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddUnmergedLane("harness/unique-tip");
        if (detached) CleanLanesFixture.Git(lane, "switch", "--detach");
        var head = fixture.Head(lane);
        AssertLockedContentRetained(fixture, lane, "locked_history");
        Assert.Equal(head, fixture.Head(lane));
        Assert.True(fixture.BranchExists("harness/unique-tip"));
    }

    [Fact]
    public void DetachedWorktreeOnlyReflogHistorySurvivesResetToRetainedTip()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/reflog-only");
        var retainedTip = fixture.Head(lane);
        CleanLanesFixture.Git(lane, "switch", "--detach");
        File.AppendAllText(Path.Combine(lane, "README.md"), "committed only here\n");
        CleanLanesFixture.Git(lane, "add", "README.md");
        CleanLanesFixture.Git(lane, "commit", "-m", "worktree only history");
        var uniqueTip = fixture.Head(lane);
        CleanLanesFixture.Git(lane, "reset", "--hard", retainedTip);
        Assert.DoesNotContain(uniqueTip, CleanLanesFixture.Git(lane, "for-each-ref", "--format=%(objectname)"));
        var log = Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD");
        var before = File.ReadAllBytes(log);
        AssertLockedContentRetained(fixture, lane, "locked_history");
        Assert.Equal(before, File.ReadAllBytes(log));
        Assert.Contains(uniqueTip, File.ReadAllText(log));
    }

    [Fact]
    public void CleanupOwnedOrphanBaseIsNotSoleHistoryRetentionEvidence()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddUnmergedLane("harness/unique-history");
        var uniqueTip = fixture.Head(lane);
        var temporaryBase = CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory,
            "commit-tree", "dev^{tree}", "-p", "dev", "-p", uniqueTip, "-m", "temporary base").Trim();
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "branch", "harness/transient-base", temporaryBase);
        fixture.LockLane(lane, InitializationLock);
        var result = fixture.RunWithBase("harness/transient-base", "--force");
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("locked_history", ReasonFor(result.Output, lane));
        Assert.Equal(uniqueTip, fixture.Head(lane));
        Assert.True(fixture.BranchExists("harness/unique-history"));
        Assert.False(fixture.BranchExists("harness/transient-base"));
    }

    [Theory]
    [InlineData("refs/heads/retained-base")]
    [InlineData("refs/remotes/origin/retained-base")]
    [InlineData("refs/tags/retained-base")]
    public void SurvivingRefCanRetainBaseAheadOfCurrentCheckout(string reference)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/retained-base");
        var futureBase = CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory,
            "commit-tree", "dev^{tree}", "-p", "dev", "-m", "retained future base").Trim();
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "update-ref", reference, futureBase);
        fixture.LockLane(lane, InitializationLock);
        var result = fixture.RunWithBase(reference, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane), result.Output);
        Assert.Equal(futureBase, CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory,
            "rev-parse", reference).Trim());
    }

    [Fact]
    public void EmptyReviewCheckoutWithoutIndexRemainsReclaimable()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/empty-review");
        fixture.RemoveWorktreeIndex(lane);
        foreach (var file in Directory.EnumerateFiles(lane))
            if (Path.GetFileName(file) != ".git") File.Delete(file);
        fixture.LockLane(lane, InitializationLock);
        var result = fixture.Run("--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane), result.Output);
    }

    private static void AssertLockedContentRetained(CleanLanesFixture fixture, string lane, string reason)
    {
        fixture.LockLane(lane, InitializationLock);
        var index = Path.Combine(fixture.WorktreeGitDirectory(lane), "index");
        var before = File.Exists(index) ? File.ReadAllBytes(index) : null;
        foreach (var args in new[] { new[] { "--lanes-only" }, new[] { "--force", "--lanes-only" } })
        {
            var result = fixture.Run(args);
            Assert.True(result.Success, result.Error);
            Assert.True(Directory.Exists(lane));
            Assert.Equal(reason, ReasonFor(result.Output, lane));
            Assert.Equal(before, File.Exists(index) ? File.ReadAllBytes(index) : null);
            Assert.Equal(InitializationLock,
                File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
        }
    }
}
