using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
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
        Assert.Contains(ReadItems(preview.Output), item => ItemMatches(item, lane, "would_remove", "stale_lock"));
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
