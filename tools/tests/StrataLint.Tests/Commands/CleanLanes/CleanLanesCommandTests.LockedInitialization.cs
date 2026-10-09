using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void StaleInitializationLockWithMatchingCheckoutIsReclaimed()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/initialization-stale");
        fixture.LockLane(lane, "worktree-init:01234567890123456789012345678901");

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane), result.Output);
        Assert.Equal("stale_behind", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void PreviewReportsStaleInitializationLockWithoutChangingTheTree()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/initialization-preview");
        fixture.LockLane(lane, "worktree-init:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");

        var result = fixture.Run("--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Contains(
            ReadItems(result.Output),
            item => ItemMatches(item, lane, "would_remove", "stale_initialization_lock"));
    }

    [Fact]
    public void MissingIndexAndOldEmptyIndexLockUseCheckoutEvidence()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/initialization-missing-index");
        fixture.LockLane(lane, "worktree-init:abcdefabcdefabcdefabcdefabcdefab");
        fixture.RemoveWorktreeIndex(lane);
        fixture.WriteOldEmptyIndexLock(lane);
        File.Delete(Path.Combine(lane, "README.md"));

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal("stale_behind", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void InitializationLockWithNewContentIsRetained()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/initialization-content");
        File.WriteAllText(Path.Combine(lane, "new-theory.md"), "new material\n");
        fixture.LockLane(lane, "worktree-init:11111111111111111111111111111111");

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("locked_content", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void InitializationLockWithRecentIndexActivityIsRetained()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/initialization-active");
        fixture.LockLane(lane, "worktree-init:22222222222222222222222222222222");
        var indexLock = Path.Combine(fixture.WorktreeGitDirectory(lane), "index.lock");
        File.WriteAllBytes(indexLock, [1]);

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("locked_activity", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void ActiveInitializationLockIsRetained()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/initialization-host-active");
        fixture.LockLane(lane, "worktree-init:44444444444444444444444444444444");

        var result = fixture.RunWithActivePath(lane, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("locked_activity", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void MalformedInitializationLockIsRetainedAsUnknown()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/initialization-malformed");
        fixture.LockLane(lane, "worktree-init:not-a-token");

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("locked_unknown", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void InitializationLockIdentityChangeIsRefusedAtDeletion()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/initialization-lock-race");
        fixture.LockLane(lane, "worktree-init:33333333333333333333333333333333");
        var production = new ProductionWorktreeProcessRunner();
        var inventoryCalls = 0;
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
        {
            if (fileName == "git"
                && arguments.SequenceEqual(["worktree", "list", "--porcelain", "-z"])
                && ++inventoryCalls == 2)
            {
                var unlock = production.Run(
                    "git",
                    ["worktree", "unlock", lane],
                    fixture.RepositoryWorkingDirectory,
                    BoundedProcessRunner.HangDetectionBudget);
                Assert.Equal(0, unlock.ExitCode);
            }

            return null;
        });

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("locked_changed", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void LockedParentIsRetainedWhenNestedTreeIsRetained()
    {
        using var fixture = new CleanLanesFixture();
        var parent = fixture.AddLandedLane("harness/initialization-parent");
        var child = fixture.AddNestedWorktree(parent);
        fixture.LockLane(parent, "worktree-init:55555555555555555555555555555555");
        fixture.LockLane(child);

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(parent));
        Assert.True(Directory.Exists(child));
        Assert.Equal("nested_worktree", ReasonFor(result.Output, parent));
        Assert.Equal("locked_intentional", ReasonFor(result.Output, child));
    }
}
