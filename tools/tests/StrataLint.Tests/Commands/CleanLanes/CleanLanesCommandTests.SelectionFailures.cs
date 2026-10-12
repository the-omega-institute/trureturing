using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void MalformedReflogIdentityRetainsLane()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/corrupt-identity");
        var log = Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD");
        var lines = File.ReadAllLines(log);
        var tab = lines[^1].IndexOf('\t');
        var fields = lines[^1][..tab].Split(' ', StringSplitOptions.RemoveEmptyEntries);
        lines[^1] = $"{fields[0]} {fields[1]} missing email {fields[^2]} {fields[^1]}\tcommit: lane work";
        File.WriteAllLines(log, lines);

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("update_unknown", ReasonFor(result.Output, lane));
        AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_detail", "reflog_invalid");
    }

    [Theory]
    [InlineData("")]
    [InlineData("   ")]
    public void BlankReflogCommitterRetainsLane(string name)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/blank-identity");
        var log = Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD");
        var lines = File.ReadAllLines(log);
        var parts = lines[^1].Split('\t', 2);
        var fields = parts[0].Split(' ', StringSplitOptions.RemoveEmptyEntries);
        lines[^1] = $"{fields[0]} {fields[1]} {name} <test@example.invalid> {fields[^2]} {fields[^1]}\t{parts[1]}";
        File.WriteAllLines(log, lines);

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal("update_unknown", ReasonFor(result.Output, lane));
        AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_detail", "reflog_invalid");
        Assert.True(Directory.Exists(lane));
    }

    [Theory]
    [InlineData("status", "unreadable")]
    [InlineData("commit", "update_unknown")]
    public void UnreadableShortcutPrerequisitesRetainLane(string failure, string reason)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/unknown-state");
        var runner = fixture.CreateRunner((file, args, directory) => file == "git" && directory == lane
            && args[0] == (failure == "status" ? "status" : "show")
                ? GitFailure("shortcut prerequisite failed") : null);

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal(reason, ReasonFor(result.Output, lane));
    }

    [Fact]
    public void MissingDefaultDevIsReportedWithoutSelectingARegisteredTree()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/missing-default-dev");
        var runner = fixture.CreateRunner((file, args, _) => file == "git"
            && args.Contains("refs/remotes/origin/dev^{commit}") ? GitFailure("missing dev") : null);

        var result = CleanLanesCommand.Run(fixture.RepositoryWorkingDirectory,
            ["--force", "--lanes-only"], runner, [], fixture.LastUpdate(lane).AddDays(2));

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("dev_unknown", ReasonFor(result.Output, lane));
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
