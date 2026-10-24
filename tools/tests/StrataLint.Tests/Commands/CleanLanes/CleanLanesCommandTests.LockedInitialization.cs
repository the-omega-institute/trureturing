using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void CurrentInitializationMarkerUsesExclusiveScopeLiveness()
    {
        using var fixture = new CleanLanesFixture();
        var branch = "harness/current-initialization";
        var lane = fixture.AddLandedLane(branch);
        fixture.LockLane(lane, "worktree-init:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
        File.SetLastWriteTimeUtc(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked"),
            new DateTime(2030, 1, 2, 0, 0, 0, DateTimeKind.Utc));
        using (WorktreeInitializationScope.Acquire(lane, lane, branch))
        {
            var alive = fixture.Run("--force", "--lanes-only");
            Assert.Equal("initialization_in_progress", ReasonFor(alive.Output, lane));
            Assert.True(Directory.Exists(lane));
        }
        var dead = fixture.Run("--force", "--lanes-only");
        Assert.True(dead.Success, dead.Error);
        Assert.False(Directory.Exists(lane), dead.Output);
    }

    [Theory]
    [InlineData("manual")]
    [InlineData("worktree-init:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
    [InlineData("worktree-init:malformed")]
    [InlineData("")]
    public void ElapsedLocksUseTheSameRemovalPolicy(string reason)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/elapsed-lock");
        fixture.LockLane(lane, reason);
        var preview = fixture.Run("--lanes-only");
        Assert.True(preview.Success, preview.Error);
        Assert.Contains(ReadItems(preview.Output), item => ItemMatches(item, lane, "would_remove", "merged_to_dev"));
        Assert.True(Directory.Exists(lane));
        var result = fixture.Run("--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane), result.Output);
    }

    [Fact]
    public void CurrentLockIsRetainedByAutomaticSelection()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/current-lock");
        fixture.LockLane(lane);
        File.SetLastWriteTimeUtc(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked"),
            new DateTime(2030, 1, 2, 0, 0, 0, DateTimeKind.Utc));
        var result = fixture.Run("--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.Equal("locked_recent", ReasonFor(result.Output, lane));
        Assert.True(Directory.Exists(lane));
    }
}
