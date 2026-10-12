using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MergedWorkedCleanLaneBypassesAgeAndBehind(bool force)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/merged-work");
        var head = fixture.Head(lane);
        var arguments = force ? new[] { "--lanes-only", "--force" } : ["--lanes-only"];

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddMinutes(1), arguments);

        Assert.True(result.Success, result.Error);
        Assert.Contains(ReadItems(result.Output), item =>
            ItemMatches(item, lane, force ? "removed" : "would_remove", "merged_to_dev"));
        Assert.Equal(!force, Directory.Exists(lane));
        Assert.True(fixture.BranchExists("harness/merged-work"));
        Assert.Equal(head, ReadSummary(result.Output).GetProperty("dev_commit").GetString());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void NewLaneAtDevHasNoWorkWitness(bool reset)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddMergedLane("harness/new-task");
        if (reset) CleanLanesFixture.Git(lane, "reset", "--hard", "HEAD");
        else fixture.KeepInitializationRecord(lane);

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddMinutes(1), "--lanes-only", "--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("recently_updated", ReasonFor(result.Output, lane));
        AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_reason", "merged_without_work_witness");
    }

    [Fact]
    public void ReusedLaneCheckedOutToDevDoesNotReuseOldCommitWitness()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/reused-task");
        fixture.AdvanceBase(1);
        CleanLanesFixture.Git(lane, "checkout", "--detach", "dev");

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddMinutes(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("recently_updated", ReasonFor(result.Output, lane));
        AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_reason", "merged_without_work_witness");
    }

    [Theory]
    [InlineData("tracked", false)]
    [InlineData("untracked", false)]
    [InlineData("staged", false)]
    [InlineData("untracked", true)]
    public void MergedDirtyLaneUsesOriginalSelectorsAndCheckpoint(string shape, bool stale)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/dirty-landed");
        var file = Path.Combine(lane, shape == "tracked" ? "README.md" : "changes.txt");
        File.WriteAllText(file, "recover this snapshot\n");
        if (shape == "staged") CleanLanesFixture.Git(lane, "add", "changes.txt");
        if (stale) fixture.AdvanceBase(300);
        var now = fixture.LastUpdate(lane).AddSeconds(stale ? 86400 : 60);

        var result = fixture.RunAt(now, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal(!stale, Directory.Exists(lane));
        Assert.Equal(stale ? "stale_behind" : "recently_updated", ReasonFor(result.Output, lane));
        if (stale)
        {
            CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "worktree", "add", lane, "harness/dirty-landed");
            Assert.Equal("recover this snapshot\n", File.ReadAllText(file));
        }
    }

    [Theory]
    [InlineData(299, 86400, "not_far_behind")]
    [InlineData(300, 86399, "recently_updated")]
    [InlineData(300, 86400, "stale_behind")]
    public void UnmergedWorkedLaneStillRequiresBothBoundaries(int behind, int seconds, string reason)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/unmerged-work", landed: false);
        fixture.AdvanceBase(behind);
        var now = fixture.LastUpdate(lane).AddSeconds(seconds);

        var preview = fixture.RunAt(now, "--lanes-only");
        var force = fixture.RunAt(now, "--force", "--lanes-only");

        Assert.True(preview.Success, preview.Error);
        Assert.True(force.Success, force.Error);
        Assert.Equal(reason, ReasonFor(preview.Output, lane));
        Assert.Equal(reason, ReasonFor(force.Output, lane));
        Assert.Equal(reason != "stale_behind", Directory.Exists(lane));
    }

    [Fact]
    public void AlternateBaseCannotCertifyLaneMergedToDev()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/alternate-base-only";
        var lane = fixture.AddWorkedLane(branch, landed: false);

        var result = fixture.RunWithBase(branch, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("not_far_behind", ReasonFor(result.Output, lane));
        Assert.Equal(fixture.Head(fixture.RepositoryWorkingDirectory),
            ReadSummary(result.Output).GetProperty("dev_commit").GetString());
    }

    [Fact]
    public void AlternateBaseCannotPreventActualDevMergeShortcut()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/landed-before-base");
        var oldBase = CleanLanesFixture.Git(lane, "rev-parse", "HEAD^").Trim();

        var result = fixture.RunWithBase(oldBase, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal("merged_to_dev", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData("missing", "reflog_missing")]
    [InlineData("corrupt", "reflog_invalid")]
    [InlineData("mismatch", "reflog_head_mismatch")]
    public void UnreadableWorkWitnessRetainsLaneWithNamedReason(string shape, string detail)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/unknown-witness");
        fixture.AdvanceBase(300);
        var log = Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD");
        if (shape == "missing") File.Delete(log);
        else if (shape == "corrupt") File.AppendAllText(log, "not a reflog record\n");
        else fixture.RewriteLastRecord(lane, newHead: CleanLanesFixture.Git(lane, "rev-parse", "HEAD^").Trim());

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("work_witness_unknown", ReasonFor(result.Output, lane));
        AssertItemProperty(ReadItems(result.Output), "path", lane, "work_witness_reason", detail);
    }

    [Theory]
    [InlineData("dev")]
    [InlineData("ancestry")]
    public void UnknownMergeEvidenceRetainsEvenOldFarBehindLane(string failure)
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
        Assert.True(Directory.Exists(lane));
        Assert.Equal(failure == "dev" ? "dev_unknown" : "merged_state_unknown", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData("head")]
    [InlineData("branch")]
    [InlineData("witness")]
    [InlineData("dirty")]
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
                else if (change == "dirty") File.WriteAllText(Path.Combine(lane, "new-task.txt"), "new task\n");
                else fixture.RewriteLastRecord(lane, message: "reset: moving to HEAD");
            }
            return null;
        });

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(injected);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("race_changed", ReasonFor(result.Output, lane));
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
        Assert.Equal("merged_to_dev", ReasonFor(result.Output, lane));
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

        internal void RewriteLastRecord(string path, string? message = null, string? newHead = null, string? oldHead = null)
        {
            var log = CreationLogPath(path);
            var lines = File.ReadAllLines(log);
            var parts = lines[^1].Split('\t', 2);
            var fields = parts[0].Split(' ');
            if (oldHead is not null) fields[0] = oldHead;
            if (newHead is not null) fields[1] = newHead;
            lines[^1] = string.Join(' ', fields) + "\t" + (message ?? parts[1]);
            File.WriteAllLines(log, lines, new UTF8Encoding(false));
        }
    }
}
