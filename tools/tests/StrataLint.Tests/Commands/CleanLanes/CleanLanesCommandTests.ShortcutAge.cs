using System.Globalization;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(10799, false)]
    [InlineData(10800, true)]
    public void MergedCleanLaneRequiresThreeHoursOfSavedWorkAndAllocationAge(int seconds, bool reclaim)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/shortcut-age");
        var now = fixture.LastUpdate(lane).AddSeconds(seconds);

        var preview = fixture.RunAt(now, "--lanes-only");
        var force = fixture.RunAt(now, "--force", "--lanes-only");

        Assert.True(preview.Success, preview.Error);
        Assert.True(force.Success, force.Error);
        Assert.Empty(ReadEvents(preview.Error, "clean_lanes_warning"));
        Assert.Empty(ReadEvents(force.Error, "clean_lanes_warning"));
        Assert.Equal(reclaim ? "merged_to_dev" : "recently_updated", ReasonFor(preview.Output, lane));
        Assert.Equal(reclaim ? "merged_to_dev" : "recently_updated", ReasonFor(force.Output, lane));
        Assert.Equal(!reclaim, Directory.Exists(lane));
        Assert.True(fixture.BranchExists("harness/shortcut-age"));
    }

    [Theory]
    [InlineData(false, 10799, false)]
    [InlineData(false, 10800, true)]
    [InlineData(true, 10799, false)]
    [InlineData(true, 10800, true)]
    public void FreshMergedAllocationRequiresThreeHoursEvenAfterReset(bool reset, int seconds, bool reclaim)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddMergedLane("harness/new-shortcut-age");
        if (reset) CleanLanesFixture.Git(lane, "reset", "--hard", "HEAD");
        else fixture.KeepInitializationRecord(lane);
        var now = fixture.CreationTime(lane).AddSeconds(seconds);

        var preview = fixture.RunAt(now, "--lanes-only");
        var force = fixture.RunAt(now, "--force", "--lanes-only");

        Assert.True(preview.Success, preview.Error);
        Assert.True(force.Success, force.Error);
        Assert.Equal(reclaim ? "merged_to_dev" : "recently_updated", ReasonFor(preview.Output, lane));
        Assert.Equal(reclaim ? "merged_to_dev" : "recently_updated", ReasonFor(force.Output, lane));
        Assert.Equal(!reclaim, Directory.Exists(lane));
        Assert.True(fixture.BranchExists("harness/new-shortcut-age"));
    }

    [Theory]
    [InlineData("tracked")]
    [InlineData("untracked")]
    [InlineData("staged")]
    public void MergedDirtyLaneAtThreeHoursUsesOriginalAgeRule(string shape)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/dirty-shortcut-age");
        var file = Path.Combine(lane, shape == "tracked" ? "README.md" : "changes.txt");
        File.WriteAllText(file, "recover this snapshot\n");
        if (shape == "staged") CleanLanesFixture.Git(lane, "add", "changes.txt");
        fixture.AdvanceBase(300);
        var now = fixture.LastUpdate(lane).AddSeconds(10800);

        var preview = fixture.RunAt(now, "--lanes-only");
        var force = fixture.RunAt(now, "--force", "--lanes-only");

        Assert.True(preview.Success, preview.Error);
        Assert.True(force.Success, force.Error);
        Assert.Equal("recently_updated", ReasonFor(preview.Output, lane));
        Assert.Equal("recently_updated", ReasonFor(force.Output, lane));
        Assert.True(Directory.Exists(lane));
        Assert.Equal("recover this snapshot\n", File.ReadAllText(file));
    }

    [Theory]
    [InlineData("head-commit", -1, "age_unverifiable")]
    [InlineData("head-commit", 10799, "recently_updated")]
    [InlineData("head-commit", 10800, "merged_to_dev")]
    [InlineData("earlier-reflog", -1, "age_unverifiable")]
    [InlineData("earlier-reflog", 10799, "recently_updated")]
    [InlineData("earlier-reflog", 10800, "merged_to_dev")]
    public void MergedShortcutRequiresBothCommitAndFirstRecordAge(string source, int seconds, string reason)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/latest-update-age");
        var committed = DateTimeOffset.FromUnixTimeSeconds(long.Parse(
            CleanLanesFixture.Git(lane, "show", "-s", "--format=%ct", "HEAD").Trim(),
            CultureInfo.InvariantCulture));
        var latest = source == "earlier-reflog" ? committed.AddDays(1) : committed;
        var log = Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD");
        var lines = File.ReadAllLines(log);
        for (var index = 0; index < lines.Length; index++)
        {
            var parts = lines[index].Split('\t', 2);
            var fields = parts[0].Split(' ');
            var timestamp = source == "earlier-reflog" && index == 0 ? latest : committed.AddDays(-1);
            fields[^2] = timestamp.ToUnixTimeSeconds().ToString(CultureInfo.InvariantCulture);
            lines[index] = string.Join(' ', fields) + (parts.Length == 2 ? "\t" + parts[1] : "");
        }
        File.WriteAllLines(log, lines);
        var now = latest.AddSeconds(seconds);

        var preview = fixture.RunAt(now, "--lanes-only");
        var force = fixture.RunAt(now, "--force", "--lanes-only");

        Assert.True(preview.Success, preview.Error);
        Assert.True(force.Success, force.Error);
        Assert.Equal(reason, ReasonFor(preview.Output, lane));
        Assert.Equal(reason, ReasonFor(force.Output, lane));
        Assert.Equal(reason != "merged_to_dev", Directory.Exists(lane));
    }
}
