using System.Runtime.ExceptionServices;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void RootUsageListsCleanLanesCommand()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [],
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("clean-lanes", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ParseUsesDryRunAndDevBaseByDefault()
    {
        var options = CleanLanesCommand.ParseArguments([]);

        Assert.Equal("origin/dev", options.Base);
        Assert.False(options.Force);
        Assert.False(options.LanesOnly);
    }

    [Fact]
    public void ParseAcceptsLanesOnlyScope()
    {
        var options = CleanLanesCommand.ParseArguments(["--lanes-only", "--force"]);

        Assert.True(options.LanesOnly);
        Assert.True(options.Force);
    }

    [Theory]
    [InlineData("--unknown")]
    [InlineData("--base")]
    [InlineData("--force", "--force")]
    [InlineData("--lanes-only", "--lanes-only")]
    public void ParseRejectsUnknownMissingOrDuplicateArguments(params string[] arguments)
    {
        var exception = Assert.Throws<InvalidOperationException>(() =>
            CleanLanesCommand.ParseArguments(arguments));

        Assert.Contains("USAGE: StrataLint clean-lanes", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void UnreadableRegisteredLaneIsSkippedWithoutHidingHealthyLanes()
    {
        using var fixture = new CleanLanesFixture();
        var unreadable = fixture.AddLandedLane("harness/unreadable");
        var healthy = fixture.AddLandedLane("harness/healthy");
        File.Delete(Path.Combine(unreadable, ".git"));

        Assert.True(Directory.Exists(unreadable));
        Assert.False(File.Exists(Path.Combine(unreadable, ".git")));

        var result = fixture.Run();

        Assert.True(result.Success, result.Error);
        var items = ReadItems(result.Output);
        Assert.Contains(items, item =>
            ItemMatches(item, unreadable, "skipped", "unreadable"));
        Assert.Contains(items, item =>
            ItemMatches(item, healthy, "would_remove", "stale_behind"));
    }

    [Fact]
    public void BaseResolutionFailureRemainsFailClosed()
    {
        using var fixture = new CleanLanesFixture();
        var runner = new SelectiveFailureRunner(
            arguments => arguments.Count > 0
                && arguments[0] == "rev-parse"
                && arguments[^1] == "dev^{commit}",
            "synthetic base resolution failure");

        var result = fixture.RunWith(runner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Equal("CLEAN_LANES_FAILED synthetic base resolution failure\n", result.Error);
    }

    [Fact]
    public void WorktreeEnumerationFailureRemainsFailClosed()
    {
        using var fixture = new CleanLanesFixture();
        var runner = new SelectiveFailureRunner(
            arguments => arguments.Count > 1
                && arguments[0] == "worktree"
                && arguments[1] == "list",
            "synthetic worktree enumeration failure");

        var result = fixture.RunWith(runner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Equal("CLEAN_LANES_FAILED synthetic worktree enumeration failure\n", result.Error);
    }

    [Fact]
    public void ForceRemovesGitlessJudgeSnapshotButKeepsReportDirectory()
    {
        using var fixture = new CleanLanesFixture();
        var judge = fixture.AddGitlessJudgeSnapshot("trureturing-snapshot-judge");
        var reports = fixture.AddReportDirectory("trureturing-report-files");

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(judge));
        Assert.True(Directory.Exists(reports));
        var items = ReadItems(result.Output);
        AssertItemProperty(items, "path", judge, "reason", "gitless_judge_snapshot");
        AssertItemProperty(items, "path", reports, "reason", "not_judge_tree");
    }

    [Fact]
    public void ForceReportsWorktreeRemovalFailureAndReclaimsHealthyLane()
    {
        using var fixture = new CleanLanesFixture();
        const string retainedBranch = "harness/remove-failure-a-retained";
        const string removedBranch = "harness/remove-failure-z-control";
        var retained = fixture.AddLandedLane(retainedBranch);
        var removed = fixture.AddLandedLane(removedBranch);
        var runner = new SelectiveFailureRunner(
            arguments => arguments.Count > 1
                && arguments[0] == "worktree"
                && arguments[1] == "remove"
                && arguments.Contains(retained, StringComparer.Ordinal),
            "synthetic worktree removal failure");

        var result = fixture.RunWith(runner, "--force", "--lanes-only");

        Assert.False(result.Success);
        Assert.Equal("CLEAN_LANES_PARTIAL_FAILURE count=1\n", result.Error);
        Assert.True(Directory.Exists(retained));
        Assert.True(fixture.BranchExists(retainedBranch));
        Assert.False(Directory.Exists(removed));
        Assert.False(fixture.BranchExists(removedBranch));
        Assert.Contains(ReadItems(result.Output), item =>
            ItemMatches(
                item,
                retained,
                "partially_removed",
                "worktree_remove_failed_state_indeterminate"));
        Assert.Contains(ReadItems(result.Output), item =>
            ItemMatches(item, removed, "removed", "stale_behind"));
        Assert.Contains("\"event\":\"clean_lanes_summary\"", result.Output, StringComparison.Ordinal);
        var summary = ReadSummary(result.Output);
        Assert.Equal(1, summary.GetProperty("partial_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removable_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removed_count").GetInt32());
    }

    [Fact]
    public void LockedLaneIsRefusedWhileUnlockedControlIsReclaimed()
    {
        using var fixture = new CleanLanesFixture();
        var locked = fixture.AddLandedLane("harness/locked");
        var unlocked = fixture.AddLandedLane("harness/unlocked");
        fixture.LockLane(locked);

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(locked));
        Assert.False(Directory.Exists(unlocked));
        Assert.Equal("locked", ReasonFor(result.Output, locked));
        Assert.Equal("stale_behind", ReasonFor(result.Output, unlocked));
    }

    [Theory]
    [InlineData(299, 86400, false)]
    [InlineData(300, 86399, false)]
    [InlineData(300, 86400, true)]
    [InlineData(301, 86401, true)]
    [InlineData(300, -1, false)]
    public void ExactInactivityAndBehindBoundaries(int behind, int seconds, bool removable)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddMergedLane("harness/boundary");
        fixture.AdvanceBase(behind);
        var now = fixture.LastUpdate(lane).AddSeconds(seconds);

        var preview = fixture.RunAt(now, "--lanes-only");
        Assert.True(preview.Success, preview.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal(removable ? 1 : 0, ReadSummary(preview.Output).GetProperty("removable_count").GetInt32());
        var result = fixture.RunAt(now, "--lanes-only", "--force");
        Assert.True(result.Success, result.Error);
        Assert.Equal(!removable, Directory.Exists(lane));
        Assert.Equal(ReasonFor(preview.Output, lane), ReasonFor(result.Output, lane));
    }

    [Fact]
    public void DirtyDivergedWorktreeIsForceRemovedWithoutStatusPrOrProcessQueries()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddUnmergedLane("harness/dirty-unmerged");
        File.WriteAllText(Path.Combine(lane, "README.md"), "unstaged change");
        File.WriteAllText(Path.Combine(lane, "untracked.txt"), "untracked change");
        File.WriteAllText(Path.Combine(lane, "staged.txt"), "staged change");
        ReviewRegressionTests.RunGit(lane, "add", "staged.txt");
        var runner = fixture.CreateRunner();

        var result = fixture.RunWithRaw(runner, "--lanes-only", "--force");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.False(fixture.BranchExists("harness/dirty-unmerged"));
        Assert.DoesNotContain(runner.Invocations, invocation => invocation.FileName != "git"
            || invocation.Arguments[0] is "status" or "merge-base");
        var removal = Assert.Single(runner.Invocations, invocation =>
            invocation.Arguments.Take(2).SequenceEqual(new[] { "worktree", "remove" }));
        Assert.Equal(new[] { "worktree", "remove", "--force", "--", lane }, removal.Arguments);
    }

    [Fact]
    public void RecentHeadActivityProtectsOldCheckoutEvenAfterResetToOldCommit()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/recent-reset");
        var now = fixture.LastUpdate(lane).AddDays(2);
        fixture.RewriteLastUpdate(lane, now.AddHours(-1));

        var result = fixture.RunAt(now, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("recently_updated", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("empty")]
    [InlineData("malformed")]
    public void UnverifiableUpdateIsRetained(string shape)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/update-unknown");
        if (shape == "missing") fixture.DeleteCreationLog(lane);
        else if (shape == "empty") fixture.EmptyCreationLog(lane);
        else
        {
            var gitDirectory = ReviewRegressionTests.RunGit(lane, "rev-parse", "--absolute-git-dir").Trim();
            File.AppendAllText(Path.Combine(gitDirectory, "logs", "HEAD"), "malformed\n");
        }

        var result = fixture.Run("--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("update_unknown", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData("garbage")]
    [InlineData("")]
    [InlineData("-1")]
    public void UnverifiableBehindCountIsRetained(string output)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/behind-unknown");
        var runner = fixture.CreateRunner((file, args, directory) => args[0] == "rev-list"
            ? new ProcessOutput(0, Encoding.UTF8.GetBytes(output), []) : null);
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("behind_unknown", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void ActivityBetweenClassificationAndRemovalPreventsDeletion()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/updated-during-sweep");
        var reads = 0;
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            if (args[0] == "worktree" && args[1] == "list" && ++reads == 2)
                fixture.RewriteLastUpdate(lane, new DateTimeOffset(2030, 1, 2, 0, 0, 0, TimeSpan.Zero));
            return null;
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("recently_updated", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DetachedWorktreesUseSamePolicyInBothScopes(bool lanesOnly)
    {
        using var fixture = new CleanLanesFixture();
        var stale = fixture.AddDetachedJudge("trureturing-old-detached");
        fixture.AdvanceBase(300);
        var recent = fixture.AddDetachedJudge("trureturing-recent-detached");
        var args = lanesOnly ? new[] { "--force", "--lanes-only" } : new[] { "--force" };
        var result = fixture.Run(args);
        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(stale));
        Assert.True(Directory.Exists(recent));
        Assert.Equal("not_far_behind", ReasonFor(result.Output, recent));
    }

    [Fact]
    public void LanesOnlySpareOrphanBranchesAndUnregisteredSnapshots()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/scoped");
        fixture.AddOrphan("harness/orphan", merged: true);
        var snapshot = fixture.AddGitlessJudgeSnapshot("trureturing-snapshot");
        var result = fixture.Run("--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.True(fixture.BranchExists("harness/orphan"));
        Assert.True(Directory.Exists(snapshot));
    }

    [Fact]
    public void CurrentAndMainWorktreesAreAlwaysRetained()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/current");
        var result = CleanLanesCommand.Run(lane, ["--base", "dev", "--force", "--lanes-only"],
            fixture.CreateRunner(), [], fixture.LastUpdate(lane).AddDays(2));
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.True(Directory.Exists(fixture.RepositoryRoot));
        Assert.Equal("current", ReasonFor(result.Output, lane));
        Assert.Equal("main_worktree", ReasonFor(result.Output, fixture.RepositoryRoot));
    }

    private sealed partial class CleanLanesFixture : IDisposable
    {
        internal bool BranchExists(string branch)
        {
            var result = TestProcessRunner.Run(
                "git",
                ["show-ref", "--verify", "--quiet", $"refs/heads/{branch}"],
                repository.Path,
                BoundedProcessRunner.HangDetectionBudget,
                4096);
            return result.ExitCode == 0;
        }

        public void Dispose()
        {
            var failures = new List<ExceptionDispatchInfo>();
            CaptureCleanupFailure(disposeTemp, failures);
            CaptureCleanupFailure(disposeWorktrees, failures);
            CaptureCleanupFailure(disposeRepository, failures);

            if (failures.Count == 1)
            {
                failures[0].Throw();
            }

            if (failures.Count > 1)
            {
                throw new AggregateException(
                    "multiple owned directories could not be released",
                    failures.Select(static failure => failure.SourceException));
            }
        }

        private static void CaptureCleanupFailure(
            Action cleanup,
            ICollection<ExceptionDispatchInfo> failures)
        {
            try
            {
                cleanup();
            }
            catch (Exception exception)
            {
                failures.Add(ExceptionDispatchInfo.Capture(exception));
            }
        }

        private string WorktreePath(string branch) =>
            Path.Combine(worktrees.Path, branch.Replace('/', '-'));

        private string CreationLogPath(string path) =>
            Path.Combine(
                Git(path, "rev-parse", "--absolute-git-dir").Trim(),
                "logs",
                "HEAD");

        private void AddWorktree(string branch, string path) =>
            Git(repository.Path, "worktree", "add", "-b", branch, path, "dev");

        private static string Git(string root, params string[] arguments) =>
            ReviewRegressionTests.RunGit(root, arguments);
    }

    private sealed class SelectiveFailureRunner(
        Func<IReadOnlyList<string>, bool> shouldFail,
        string error) : IWorktreeProcessRunner
    {
        private readonly ProductionWorktreeProcessRunner inner = new();

        public ProcessOutput Run(
            string fileName,
            IReadOnlyList<string> arguments,
            string workingDirectory,
            TimeSpan timeout) =>
            fileName == "git" && shouldFail(arguments)
                ? new ProcessOutput(128, [], Encoding.UTF8.GetBytes(error + "\n"))
                : inner.Run(fileName, arguments, workingDirectory, timeout);
    }
}
