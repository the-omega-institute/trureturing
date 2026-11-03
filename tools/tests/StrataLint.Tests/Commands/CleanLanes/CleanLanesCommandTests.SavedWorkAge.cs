using System.Globalization;
using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(-1, false)]
    [InlineData(10800, false)]
    [InlineData(86399, false)]
    [InlineData(86400, true)]
    [InlineData(86401, true)]
    public void HeadCommitAgeRequiresAtLeastTwentyFourHours(int seconds, bool reclaim)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/commit-age-boundary", landed: false);
        var now = fixture.CommitTime(lane).AddSeconds(seconds);
        var preview = fixture.RunAt(now, "--lanes-only");
        var force = fixture.RunAt(now, "--force", "--lanes-only");
        Assert.True(preview.Success, preview.Error);
        Assert.True(force.Success, force.Error);
        var reason = reclaim ? "head_commit_age" : seconds < 0 ? "age_unverifiable" : "recently_updated";
        Assert.Equal(reason, ReasonFor(preview.Output, lane));
        Assert.Equal(reason, ReasonFor(force.Output, lane));
        Assert.Equal(!reclaim, Directory.Exists(lane));
        Assert.True(fixture.BranchExists("harness/commit-age-boundary"));
    }

    [Theory]
    [InlineData("tracked")]
    [InlineData("untracked")]
    [InlineData("staged")]
    public void OldUnmergedHeadWithFreshAllocationAndNoBehindCommitsIsCheckpointed(string shape)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/old-head", landed: false);
        var saved = fixture.CommitTime(lane);
        var allocated = saved.AddDays(2);
        const string branch = "harness/fresh-allocation";
        CleanLanesFixture.GitAt(lane, allocated, "switch", "-c", branch);
        var file = shape == "tracked" ? "README.md" : "ordinary.txt";
        File.WriteAllText(Path.Combine(lane, file), "recover this ordinary work\n");
        if (shape == "staged") CleanLanesFixture.Git(lane, "add", file);
        Assert.Equal("0", CleanLanesFixture.Git(lane, "rev-list", "--count", "HEAD..dev").Trim());
        var preview = fixture.RunAt(allocated.AddHours(1), "--lanes-only");
        Assert.True(preview.Success, preview.Error);
        Assert.Equal("head_commit_age", ReasonFor(preview.Output, lane));
        var force = fixture.RunAt(allocated.AddHours(1), "--force", "--lanes-only");
        Assert.True(force.Success, force.Error);
        Assert.False(Directory.Exists(lane));
        Assert.True(fixture.BranchExists("harness/old-head"));
        Assert.Equal("recover this ordinary work\n", CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory,
            "show", branch + ":" + file));
    }

    [Theory]
    [InlineData("head-missing")]
    [InlineData("head-invalid")]
    [InlineData("branch-missing")]
    [InlineData("future-allocation")]
    public void AllocationEvidenceDoesNotGateOldCommitSelection(string shape)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/allocation-independent");
        var now = fixture.CommitTime(lane).AddHours(25);
        var headLog = Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD");
        if (shape == "head-missing") File.Delete(headLog);
        else if (shape == "head-invalid") File.WriteAllText(headLog, "invalid\n");
        else if (shape == "branch-missing") File.Delete(fixture.BranchLogPath(lane));
        else fixture.RewriteAllocation(lane, now.AddDays(1));
        var result = fixture.RunAt(now, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.Equal("head_commit_age", ReasonFor(result.Output, lane));
        Assert.False(Directory.Exists(lane));
    }

    [Theory]
    [InlineData("reset")]
    [InlineData("checkout")]
    [InlineData("read")]
    public void SavedCommitAgeIsNotRenewedByObservationOrReflog(string action)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/saved-clock");
        var saved = fixture.LastUpdate(lane);
        if (action == "reset") CleanLanesFixture.Git(lane, "reset", "--hard", "HEAD");
        else if (action == "checkout") CleanLanesFixture.Git(lane, "checkout", "--detach", "HEAD");
        else
        {
            CleanLanesFixture.Git(lane, "status", "--porcelain");
            CleanLanesFixture.Git(lane, "show", "HEAD:README.md");
        }
        if (action != "read") fixture.RewriteLastUpdate(lane, saved.AddDays(1));

        var result = fixture.RunAt(saved.AddDays(1).AddHours(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal("head_commit_age", ReasonFor(result.Output, lane));
        Assert.False(Directory.Exists(lane));
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void SavedWorkClockUsesCommitterRatherThanAuthorTime(bool recentAuthor)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddMergedLane("harness/author-clock");
        var allocated = fixture.LastUpdate(lane);
        var now = allocated.AddDays(2);
        var committed = recentAuthor ? allocated : now.AddHours(-1);
        var authored = recentAuthor ? now.AddDays(1) : allocated;
        File.WriteAllText(Path.Combine(lane, "saved.txt"), "saved work\n");
        CleanLanesFixture.Git(lane, "add", "saved.txt");
        CleanLanesFixture.GitAt(lane, committed, "commit", "--date", authored.ToString("O"), "-m", "WIP: saved work");
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "merge", "--ff-only", "harness/author-clock");

        var result = fixture.RunAt(now, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal(recentAuthor ? "head_commit_age" : "recently_updated", ReasonFor(result.Output, lane));
        Assert.Equal(!recentAuthor, Directory.Exists(lane));
    }

    [Fact]
    public void RealWipCheckpointRenewsSavedWorkClock()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/wip-checkpoint");
        var observed = fixture.LastUpdate(lane);
        var allocated = observed.AddDays(-2);
        File.WriteAllText(Path.Combine(lane, "prior.txt"), "earlier recoverable unit\n");
        CleanLanesFixture.Git(lane, "add", "prior.txt");
        CleanLanesFixture.GitAt(lane, allocated, "commit", "-m", "Save earlier unit");
        fixture.RewriteAllocation(lane, allocated);
        fixture.AdvanceBase(300);
        var before = fixture.RunAt(observed.AddHours(1), "--lanes-only");
        Assert.True(before.Success, before.Error);
        Assert.Equal("head_commit_age", ReasonFor(before.Output, lane));
        File.WriteAllText(Path.Combine(lane, "wip.txt"), "recoverable unit\n");
        var message = Path.Combine(fixture.RepositoryWorkingDirectory, "wip-message");
        File.WriteAllText(message, "WIP: save recoverable unit\n");
        var checkpoint = WorktreeProtocolCommand.Run(fixture.RepositoryWorkingDirectory,
            ["checkpoint", "--path", lane, "--message-file", message], fixture.CreateRunner());
        Assert.True(checkpoint.Success, checkpoint.Error);
        Assert.Equal("WIP: save recoverable unit", CleanLanesFixture.Git(lane, "show", "-s", "--format=%s", "HEAD").Trim());
        var committed = DateTimeOffset.FromUnixTimeSeconds(long.Parse(
            CleanLanesFixture.Git(lane, "show", "-s", "--format=%ct", "HEAD").Trim(), CultureInfo.InvariantCulture));
        Assert.True(committed >= allocated.AddDays(1));

        var result = fixture.RunAt(committed.AddHours(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal("recently_updated", ReasonFor(result.Output, lane));
        Assert.True(Directory.Exists(lane));
    }

    [Fact]
    public void AbnormalWorkerExitLeavesOrdinaryBytesForRecyclingCheckpoint()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/abnormal-worker");
        var saved = fixture.Head(lane);
        var job = WorktreeProtocolCommand.Run(fixture.RepositoryWorkingDirectory,
            ["with", "--path", lane, "--write", "unsaved.txt", "--", "/bin/sh", "-c",
                "printf 'recover after abnormal exit\\n' > unsaved.txt; exit 17"], fixture.CreateRunner());
        Assert.Equal(17, job.ExitCode);
        Assert.Equal(saved, fixture.Head(lane));
        fixture.AdvanceBase(300);

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddDays(2), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal("head_commit_age", ReasonFor(result.Output, lane));
        Assert.False(Directory.Exists(lane));
        Assert.Equal("recover after abnormal exit\n", CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory,
            "show", "harness/abnormal-worker:unsaved.txt"));
    }

    [Fact]
    public void MissingHeadCommitIsReportedAsUnknownSavedWorkTime()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/missing-commit", landed: false);
        var head = fixture.Head(lane);
        File.Delete(Path.Combine(fixture.RepositoryRoot, ".git", "objects", head[..2], head[2..]));

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal("update_unknown", ReasonFor(result.Output, lane));
        AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_detail", "head_commit_unreadable");
        Assert.True(Directory.Exists(lane));
    }

    private sealed partial class CleanLanesFixture
    {
        internal DateTimeOffset CommitTime(string path) => DateTimeOffset.FromUnixTimeSeconds(long.Parse(
            Git(path, "show", "-s", "--format=%ct", "HEAD").Trim(), CultureInfo.InvariantCulture));

        internal string BranchLogPath(string path) => Path.Combine(RepositoryRoot, ".git", "logs", "refs", "heads",
            Git(path, "branch", "--show-current").Trim());

        internal void RewriteAllocation(string path, DateTimeOffset allocated)
        {
            RewriteLogTimes(CreationLogPath(path), allocated);
            RewriteLogTimes(BranchLogPath(path), allocated);
        }

        internal void RewriteLogTimes(string log, DateTimeOffset time)
        {
            var lines = File.ReadAllLines(log);
            for (var index = 0; index < lines.Length; index++)
            {
                var parts = lines[index].Split('\t', 2);
                var fields = parts[0].Split(' ');
                fields[^2] = time.ToUnixTimeSeconds().ToString(CultureInfo.InvariantCulture);
                lines[index] = string.Join(' ', fields) + (parts.Length == 2 ? "\t" + parts[1] : "");
            }
            File.WriteAllLines(log, lines);
        }

        internal static void GitAt(string path, DateTimeOffset committed, params string[] arguments)
        {
            var result = TestProcessRunner.Run("env", ["GIT_COMMITTER_DATE=" + committed.ToString("O"), "git", .. arguments],
                path, StrataLint.Runtime.BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        }
    }
}
