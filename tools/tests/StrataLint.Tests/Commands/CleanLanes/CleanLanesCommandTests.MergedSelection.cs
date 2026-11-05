using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void ReusedLaneCheckoutToOldDevDoesNotRenewSavedWorkOrAllocation()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/reused-task");
        fixture.AdvanceBase(1);
        var later = fixture.LastUpdate(lane).AddDays(2);
        CleanLanesFixture.GitAt(lane, later, "checkout", "--detach", "dev");

        var result = fixture.RunAt(later.AddHours(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal("head_commit_age", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData("tracked", false)]
    [InlineData("untracked", false)]
    [InlineData("staged", false)]
    [InlineData("untracked", true)]
    public void CommitAgeSelectedDirtyLaneIsCheckpointed(string shape, bool stale)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/dirty-landed");
        var file = Path.Combine(lane, shape == "tracked" ? "README.md" : "changes.txt");
        File.WriteAllText(file, "recover this snapshot\n");
        if (shape == "staged") CleanLanesFixture.Git(lane, "add", "changes.txt");
        if (stale) fixture.AdvanceBase(300);
        var now = fixture.LastUpdate(lane).AddSeconds(stale ? 86401 : 60);

        var result = fixture.RunAt(now, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal(!stale, Directory.Exists(lane));
        Assert.Equal(stale ? "head_commit_age" : "recently_updated", ReasonFor(result.Output, lane));
        if (stale)
        {
            CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "worktree", "add", lane, "harness/dirty-landed");
            Assert.Equal("recover this snapshot\n", File.ReadAllText(file));
        }
    }

    [Fact]
    public void AlternateBaseDoesNotVetoOldCommitRemoval()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/alternate-base-only";
        var lane = fixture.AddWorkedLane(branch, landed: false);

        var result = fixture.RunWithBase(branch, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal("head_commit_age", ReasonFor(result.Output, lane));
        Assert.Equal(fixture.Head(fixture.RepositoryWorkingDirectory),
            ReadSummary(result.Output).GetProperty("dev_commit").GetString());
    }

    [Fact]
    public void AlternateBaseDoesNotChangeCommitAgeSelection()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/landed-before-base");
        var oldBase = CleanLanesFixture.Git(lane, "rev-parse", "HEAD^").Trim();

        var result = fixture.RunWithBase(oldBase, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal("head_commit_age", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData("dev")]
    [InlineData("ancestry")]
    public void UnknownMergeEvidenceDoesNotGateOldCommitRemoval(string failure)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/unknown-merge");
        fixture.AdvanceBase(300);
        var runner = fixture.CreateRunner((file, args, _) => file == "git"
            && (failure == "dev" && args.Contains("refs/remotes/origin/dev^{commit}")
                || failure == "ancestry" && args.Take(2).SequenceEqual(["merge-base", "--is-ancestor"]))
                ? GitFailure("unobservable merge evidence") : null);

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal("head_commit_age", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData("head")]
    [InlineData("branch")]
    public void ForceReobservesSelectionAndReportsRaceChanged(string change)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/selection-race");
        var injected = false;
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            if (!injected && IsLaneGit(file, args, directory, lane, "rev-parse", "--verify", "HEAD^{commit}"))
            {
                injected = true;
                if (change == "head") CleanLanesFixture.Git(lane, "commit", "--allow-empty", "-m", "new task");
                else if (change == "branch") CleanLanesFixture.Git(lane, "switch", "-c", "harness/replacement-task");
            }
            return null;
        });

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(injected);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("race_changed", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void TabbedCommitterRetainsCorrectGitUpdateAge(bool landed)
    {
        using var fixture = new CleanLanesFixture();
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "config", "user.name", "A\tTabbed");
        var lane = fixture.AddWorkedLane("harness/tabbed-committer", landed);
        if (!landed) fixture.AdvanceBase(300);

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal(landed ? "head_commit_age" : "head_commit_age", ReasonFor(result.Output, lane));
        Assert.False(Directory.Exists(lane));
    }

    [Theory]
    [InlineData("unmerged", "head-read")]
    [InlineData("unmerged", "preservation-entry")]
    [InlineData("dirty", "head-read")]
    [InlineData("dirty", "preservation-entry")]
    public void CommitAgeSelectionCheckpointsLateOrdinaryChanges(string shape, string boundary)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/original-selector-race";
        var lane = fixture.AddWorkedLane(branch, landed: shape == "dirty");
        if (shape == "dirty") File.WriteAllText(Path.Combine(lane, "new-task.txt"), "earlier task\n");
        fixture.AdvanceBase(300);
        var head = fixture.Head(lane);
        var injected = false;
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            var trigger = boundary == "head-read"
                ? IsLaneGit(file, args, directory, lane, "rev-parse", "--verify", "HEAD^{commit}")
                : file == "python3" && args.Contains("remove") && args.Contains(lane);
            if (trigger && !injected)
            {
                injected = true;
                File.WriteAllText(Path.Combine(lane, "new-task.txt"), "latest task\n");
                File.WriteAllText(Path.Combine(lane, "README.md"), "latest tracked task\n");
            }
            return null;
        });

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(injected);
        Assert.Equal("head_commit_age", ReasonFor(result.Output, lane));
        Assert.False(Directory.Exists(lane));
        Assert.NotEqual(head, CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "rev-parse", branch).Trim());
        Assert.Equal("latest task\n", CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory,
            "show", branch + ":new-task.txt"));
        Assert.Equal("latest tracked task\n", CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory,
            "show", branch + ":README.md"));
    }

    [Fact]
    public void DevCommitIsFixedBeforeSelectionEvenIfTrackingRefMoves()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/pinned-dev");
        var dev = fixture.Head(lane);
        var old = CleanLanesFixture.Git(lane, "rev-parse", "HEAD^").Trim();
        var reads = 0;
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (file == "git" && args.Contains("refs/remotes/origin/dev^{commit}")) reads++;
            if (file == "git" && args.Take(2).SequenceEqual(["worktree", "list"]))
                CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "update-ref", "refs/remotes/origin/dev", old);
            return null;
        });

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal(1, reads);
        Assert.Equal(dev, ReadSummary(result.Output).GetProperty("dev_commit").GetString());
        Assert.Equal("head_commit_age", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void SquashMergeDoesNotLowerCommitAgeThreshold()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddMergedLane("harness/squashed");
        File.WriteAllText(Path.Combine(lane, "work.txt"), "lane work\n");
        CleanLanesFixture.Git(lane, "add", "work.txt");
        CleanLanesFixture.Git(lane, "commit", "-m", "lane work");
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "merge", "--squash", "harness/squashed");
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "commit", "-m", "squash lane work");

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddSeconds(10800), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("recently_updated", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData("MERGE_HEAD")]
    [InlineData("CHERRY_PICK_HEAD")]
    [InlineData("REVERT_HEAD")]
    [InlineData("rebase-merge")]
    [InlineData("rebase-apply")]
    [InlineData("sequencer")]
    public void UnfinishedOperationStillPreventsNativeRemoval(string marker)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/unfinished-landed");
        var path = Path.Combine(fixture.WorktreeGitDirectory(lane), marker);
        if (marker.EndsWith("HEAD", StringComparison.Ordinal)) File.WriteAllText(path, fixture.Head(lane) + "\n");
        else Directory.CreateDirectory(path);

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddSeconds(86401), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.DoesNotContain(ReadItems(result.Output), item => ItemMatches(item, lane, "removed", "head_commit_age"));
    }

    [Fact]
    public void OldDetachedHeadRetainsRecoveryBranch()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddDetachedJudge("trureturing-detached-work");
        CleanLanesFixture.Git(lane, "commit", "--allow-empty", "-m", "detached work");
        var head = fixture.Head(lane);
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "merge", "--ff-only", head);

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddSeconds(86401), "--force");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        var item = ReadItems(result.Output).Single(item => item.GetProperty("path").GetString() == lane);
        Assert.Equal("head_commit_age", item.GetProperty("reason").GetString());
        var branch = item.GetProperty("recovery_branch").GetString()!;
        Assert.True(fixture.BranchExists(branch["refs/heads/".Length..]));
        Assert.Equal(head, CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "rev-parse", branch).Trim());
    }
    private sealed partial class CleanLanesFixture
    {
        internal string AddWorkedLane(string branch, bool landed = true)
        {
            var path = AddMergedLane(branch);
            Git(path, "commit", "--allow-empty", "-m", "lane work");
            if (landed)
                Git(repository.Path, "merge", "--ff-only", branch);
            return path;
        }

        internal void KeepInitializationRecord(string path)
        {
            var log = CreationLogPath(path);
            File.WriteAllText(log, File.ReadLines(log).First() + "\n");
        }

        internal void RewriteLastRecord(string path, string? newHead = null)
        {
            var log = CreationLogPath(path);
            var lines = File.ReadAllLines(log);
            var parts = lines[^1].Split('\t', 2);
            var fields = parts[0].Split(' ');
            if (newHead is not null) fields[1] = newHead;
            lines[^1] = string.Join(' ', fields) + "\t" + parts[1];
            File.WriteAllLines(log, lines, new UTF8Encoding(false));
        }
    }
}
