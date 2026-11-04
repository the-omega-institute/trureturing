using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void UnreadableHeadCommitTimeRetainsTreeAndWarns(bool force)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/unknown-commit-time");
        var runner = fixture.CreateRunner((file, args, directory) => file == "git" && directory == lane
            && args[0] == "show" ? GitFailure("commit time unreadable") : null);
        var result = fixture.RunWithRaw(runner, force ? ["--force", "--lanes-only"] : ["--lanes-only"]);
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("update_unknown", ReasonFor(result.Output, lane));
        Assert.Single(ReadEvents(result.Error, "clean_lanes_warning"));
    }

    [Fact]
    public void MissingDefaultDevDoesNotGateOldCommitRemoval()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/missing-default-dev");
        var runner = fixture.CreateRunner((file, args, _) => file == "git"
            && args.Contains("refs/remotes/origin/dev^{commit}") ? GitFailure("missing dev") : null);
        var result = CleanLanesCommand.Run(fixture.RepositoryWorkingDirectory,
            ["--force", "--lanes-only"], runner, [], fixture.CommitTime(lane).AddHours(25));
        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal("head_commit_age", ReasonFor(result.Output, lane));
        Assert.Equal("dev_unknown", ReadSummary(result.Output).GetProperty("dev_state").GetString());
    }

    [Fact]
    public void LockTimestampChangesRetainEvenWhenTheLockRemainsOld()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/lock-timestamp-race");
        fixture.LockLane(lane);
        var file = Path.Combine(fixture.WorktreeGitDirectory(lane), "locked");
        var runner = fixture.CreateRunner((name, args, directory) =>
        {
            if (IsLaneGit(name, args, directory, lane, "rev-parse", "--verify", "HEAD^{commit}"))
                File.SetLastWriteTimeUtc(file, File.GetLastWriteTimeUtc(file).AddMinutes(1));
            return null;
        });

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("race_changed", ReasonFor(result.Output, lane));
    }
}
