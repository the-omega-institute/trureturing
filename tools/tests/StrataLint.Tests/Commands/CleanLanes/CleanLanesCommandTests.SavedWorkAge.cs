using System.Globalization;
using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
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
        Assert.Equal("merged_to_dev", ReasonFor(result.Output, lane));
        Assert.False(Directory.Exists(lane));
    }

    [Theory]
    [InlineData(false, 10799, "recently_updated")]
    [InlineData(false, 10800, "merged_to_dev")]
    [InlineData(true, 86399, "recently_updated")]
    [InlineData(true, 86400, "stale_behind")]
    public void FreshTreeAtOldCommitRequiresAllocationGrace(bool dirty, int seconds, string reason)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddMergedLane("harness/fresh-allocation", dirty);
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        fixture.RewriteAllocation(lane, allocated);
        if (dirty) fixture.AdvanceBase(300);

        var result = fixture.RunAt(allocated.AddSeconds(seconds), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal(reason, ReasonFor(result.Output, lane));
        Assert.Equal(reason == "recently_updated", Directory.Exists(lane));
        if (dirty && reason == "stale_behind")
            Assert.Equal("untracked\n", CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory,
                "show", "harness/fresh-allocation:dirty.txt"));
    }

    [Fact]
    public void NewBranchClaimOnOldTreeStartsAllocationGrace()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/old-allocation");
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        CleanLanesFixture.GitAt(lane, allocated, "switch", "-c", "harness/new-allocation");

        var recent = fixture.RunAt(allocated.AddSeconds(10799), "--lanes-only");
        var elapsed = fixture.RunAt(allocated.AddSeconds(10800), "--force", "--lanes-only");

        Assert.True(recent.Success, recent.Error);
        Assert.True(elapsed.Success, elapsed.Error);
        Assert.Equal("recently_updated", ReasonFor(recent.Output, lane));
        Assert.Equal("merged_to_dev", ReasonFor(elapsed.Output, lane));
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
        Assert.Equal(recentAuthor ? "merged_to_dev" : "recently_updated", ReasonFor(result.Output, lane));
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
        Assert.Equal("stale_behind", ReasonFor(before.Output, lane));
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

    [Theory]
    [InlineData("missing", "branch_reflog_missing")]
    [InlineData("invalid", "branch_reflog_invalid")]
    [InlineData("mismatch", "branch_reflog_head_mismatch")]
    public void UnverifiableBranchAllocationRetainsTree(string shape, string detail)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/unknown-allocation");
        var log = fixture.BranchLogPath(lane);
        if (shape == "missing") File.Delete(log);
        else if (shape == "invalid") File.WriteAllText(log, "invalid\n");
        else File.WriteAllLines(log, File.ReadAllLines(log).Take(1).ToArray());

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal("update_unknown", ReasonFor(result.Output, lane));
        AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_detail", detail);
        Assert.True(Directory.Exists(lane));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FutureAllocationIsAgeUnverifiableEvenIfOtherClockIsRecent(bool branch)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/future-allocation");
        var now = fixture.LastUpdate(lane).AddHours(1);
        fixture.RewriteLogTimes(branch ? fixture.BranchLogPath(lane)
            : Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD"), now.AddSeconds(1));

        var result = fixture.RunAt(now, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal("age_unverifiable", ReasonFor(result.Output, lane));
        Assert.True(Directory.Exists(lane));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ReflogExpiryCanOnlyExtendAllocationProtection(bool expire)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/expired-allocation");
        var allocated = fixture.LastUpdate(lane);
        var later = allocated.AddDays(2);
        CleanLanesFixture.GitAt(lane, later, "reset", "--hard", "HEAD");
        if (expire)
        {
            foreach (var log in new[] { fixture.BranchLogPath(lane), Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD") })
                File.WriteAllLines(log, File.ReadAllLines(log).TakeLast(1).ToArray());
        }

        var result = fixture.RunAt(later.AddHours(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal(expire ? "recently_updated" : "merged_to_dev", ReasonFor(result.Output, lane));
        Assert.Equal(expire, Directory.Exists(lane));
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
        Assert.Equal("stale_behind", ReasonFor(result.Output, lane));
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
