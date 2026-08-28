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
    public void DryRunListsEligibleItemsWithoutMutation()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/merged");
        fixture.AddOrphan("harness/orphan", merged: true);
        var judge = fixture.AddDetachedJudge("trureturing-gate-judge");

        var result = fixture.Run();

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.True(Directory.Exists(judge));
        Assert.True(fixture.BranchExists("harness/merged"));
        Assert.True(fixture.BranchExists("harness/orphan"));
        var items = ReadItems(result.Output);
        AssertItemProperty(items, "path", lane, "kind", "merged_worktree");
        AssertItemProperty(items, "path", lane, "action", "would_remove");
        AssertItemProperty(items, "branch", "harness/orphan", "kind", "orphan_branch");
        AssertItemProperty(items, "branch", "harness/orphan", "action", "would_remove");
        AssertItemProperty(items, "path", judge, "kind", "temp_judge");
        AssertItemProperty(items, "path", judge, "action", "would_remove");
    }

    [Fact]
    public void LanesOnlyScopeSpareOrphanBranchesAndJudgeTreesButStillReclaimsLanes()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/merged");
        fixture.AddOrphan("harness/orphan", merged: true);
        var judge = fixture.AddDetachedJudge("trureturing-gate-judge");

        // 阳性对照:同一夹具在全作用面下,三类确实都够得着——否则「没看见」
        // 只证明输入本来就不合判据,不证明作用面收窄起了作用。
        var full = fixture.Run();
        Assert.True(full.Success, full.Error);
        var fullItems = ReadItems(full.Output);
        AssertItemProperty(fullItems, "branch", "harness/orphan", "kind", "orphan_branch");
        AssertItemProperty(fullItems, "branch", "harness/orphan", "action", "would_remove");
        AssertItemProperty(fullItems, "path", judge, "kind", "temp_judge");
        AssertItemProperty(fullItems, "path", judge, "action", "would_remove");
        AssertItemProperty(fullItems, "path", lane, "action", "would_remove");

        var scoped = fixture.Run("--lanes-only", "--force");

        Assert.True(scoped.Success, scoped.Error);
        Assert.DoesNotContain("\"kind\":\"orphan_branch\"", scoped.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("\"kind\":\"temp_judge\"", scoped.Output, StringComparison.Ordinal);
        Assert.True(fixture.BranchExists("harness/orphan"));
        Assert.True(Directory.Exists(judge));

        // 收窄作用面不等于把功能关死:合格 lane 仍然被回收。
        Assert.False(Directory.Exists(lane));
        var scopedItems = ReadItems(scoped.Output);
        AssertItemProperty(scopedItems, "path", lane, "kind", "merged_worktree");
        AssertItemProperty(scopedItems, "path", lane, "action", "removed");
        Assert.Equal("lanes_only", ReadSummary(scoped.Output).GetProperty("scope").GetString());
        Assert.Equal("full", ReadSummary(full.Output).GetProperty("scope").GetString());
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
            ItemMatches(item, healthy, "would_remove", "merged_clean"));
    }

    [Fact]
    public void UnavailablePrProbeRefusesWithoutHidingHealthyLanes()
    {
        using var fixture = new CleanLanesFixture();
        var unavailable = fixture.AddLandedLane("harness/pr-unavailable");
        var healthy = fixture.AddLandedLane("harness/pr-healthy");
        fixture.FailPrProbe("harness/pr-unavailable");

        var result = fixture.Run();

        Assert.True(result.Success, result.Error);
        var items = ReadItems(result.Output);
        Assert.Contains(items, item =>
            ItemMatches(item, unavailable, "skipped", "pr_unknown"));
        Assert.Contains(items, item =>
            ItemMatches(item, healthy, "would_remove", "merged_clean"));
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
    public void BlockedWorktreesRetainEstablishedReasons()
    {
        using var fixture = new CleanLanesFixture();
        var missing = fixture.AddLandedLane("harness/missing");
        var dirty = fixture.AddLandedLane("harness/dirty", dirty: true);
        var unmerged = fixture.AddUnmergedLane("harness/unmerged");
        fixture.SwitchToManagedBranch("harness/current");
        Directory.Delete(missing, recursive: true);

        var result = fixture.Run();

        Assert.True(result.Success, result.Error);
        var items = ReadItems(result.Output);
        Assert.Contains(items, item =>
            ItemMatches(item, fixture.RepositoryRoot, "skipped", "current"));
        Assert.Contains(items, item =>
            ItemMatches(item, missing, "skipped", "missing"));
        Assert.Contains(items, item =>
            ItemMatches(item, dirty, "skipped", "dirty"));
        Assert.Contains(items, item =>
            ItemMatches(item, unmerged, "skipped", "pr_not_merged"));
    }

    [Fact]
    public void ForceRemovesEligibleHarnessItemsAndProtectsEveryEnumeratedIneligibleClass()
    {
        using var fixture = new CleanLanesFixture();
        var removable = fixture.AddLandedLane("harness/merged");
        var dirty = fixture.AddLandedLane("harness/dirty", dirty: true);
        var unmerged = fixture.AddUnmergedLane("harness/unmerged");
        fixture.AddOrphan("harness/orphan", merged: true);
        fixture.AddOrphan("harness/math/nested-orphan", merged: true);
        fixture.AddOrphan("harness/orphan-unmerged", merged: false);
        var foreign = fixture.AddForeignTempDirectory("trureturing-foreign");
        var attached = fixture.AddAttachedTempDirectory("trureturing-attached");
        fixture.SwitchToManagedBranch("harness/current");

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(removable));
        Assert.False(fixture.BranchExists("harness/merged"));
        Assert.False(fixture.BranchExists("harness/orphan"));
        Assert.False(fixture.BranchExists("harness/math/nested-orphan"));
        Assert.True(Directory.Exists(dirty));
        Assert.True(Directory.Exists(unmerged));
        Assert.True(Directory.Exists(foreign));
        Assert.True(Directory.Exists(attached));
        Assert.True(fixture.BranchExists("harness/dirty"));
        Assert.True(fixture.BranchExists("harness/unmerged"));
        Assert.True(fixture.BranchExists("harness/orphan-unmerged"));
        var items = ReadItems(result.Output);
        AssertItemProperty(items, "path", dirty, "reason", "dirty");
        AssertItemProperty(items, "path", unmerged, "reason", "pr_not_merged");
        AssertItemProperty(items, "path", foreign, "reason", "foreign_git_directory");
        AssertItemProperty(items, "path", attached, "reason", "attached_branch");
        AssertItemProperty(items, "path", fixture.RepositoryRoot, "action", "skipped");
        AssertItemProperty(items, "path", fixture.RepositoryRoot, "reason", "current");
    }

    [Fact]
    public void ForceRemovesDetachedJudgeFromTheSameRepository()
    {
        using var fixture = new CleanLanesFixture();
        var judge = fixture.AddDetachedJudge("trureturing-detached");

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(judge));
        var items = ReadItems(result.Output);
        AssertItemProperty(items, "path", judge, "kind", "temp_judge");
        AssertItemProperty(items, "path", judge, "action", "removed");
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
            ItemMatches(item, removed, "removed", "merged_clean"));
        Assert.Contains("\"event\":\"clean_lanes_summary\"", result.Output, StringComparison.Ordinal);
        var summary = ReadSummary(result.Output);
        Assert.Equal(1, summary.GetProperty("partial_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removable_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removed_count").GetInt32());
    }

    [Fact]
    public void FreshZeroCommitLaneIsRefusedWhileLandedLaneIsReclaimed()
    {
        using var fixture = new CleanLanesFixture();
        var fresh = fixture.AddMergedLane("harness/fresh-zero");
        var landed = fixture.AddLandedLane("harness/landed");

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(fresh));
        Assert.False(Directory.Exists(landed));
        Assert.Equal("never_worked", ReasonFor(result.Output, fresh));
        Assert.Equal("merged_clean", ReasonFor(result.Output, landed));
    }

    [Fact]
    public void LaneUnderTwentyFourHoursIsTooYoungWhileTwentyFourHourLaneIsReclaimed()
    {
        using var youngFixture = new CleanLanesFixture();
        var young = youngFixture.AddLandedLane("harness/young");
        var youngResult = youngFixture.RunAt(
            youngFixture.CreationTime(young).AddHours(23));

        using var oldFixture = new CleanLanesFixture();
        var old = oldFixture.AddLandedLane("harness/old");
        var oldResult = oldFixture.RunAt(
            oldFixture.CreationTime(old).AddHours(25),
            "--force");

        Assert.True(youngResult.Success, youngResult.Error);
        Assert.Equal("too_young", ReasonFor(youngResult.Output, young));
        Assert.True(oldResult.Success, oldResult.Error);
        Assert.False(Directory.Exists(old));
        Assert.Equal("merged_clean", ReasonFor(oldResult.Output, old));
    }

    [Fact]
    public void AgeBoundaryIsExactAtTwentyFourHours()
    {
        using var youngFixture = new CleanLanesFixture();
        var young = youngFixture.AddLandedLane("harness/boundary-young");
        var youngResult = youngFixture.RunAt(
            youngFixture.CreationTime(young).AddHours(24).AddSeconds(-1));

        using var boundaryFixture = new CleanLanesFixture();
        var boundary = boundaryFixture.AddLandedLane("harness/boundary-exact");
        var boundaryResult = boundaryFixture.RunAt(
            boundaryFixture.CreationTime(boundary).AddHours(24),
            "--force");

        Assert.True(youngResult.Success, youngResult.Error);
        Assert.Equal("too_young", ReasonFor(youngResult.Output, young));
        Assert.True(boundaryResult.Success, boundaryResult.Error);
        Assert.False(Directory.Exists(boundary));
        Assert.Equal("merged_clean", ReasonFor(boundaryResult.Output, boundary));
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("empty")]
    [InlineData("non_creation")]
    public void MissingEmptyOrNonCreationShapedReflogIsRefused(string shape)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane($"harness/reflog-{shape}");
        switch (shape)
        {
            case "missing":
                fixture.DeleteCreationLog(lane);
                break;
            case "empty":
                fixture.EmptyCreationLog(lane);
                break;
            case "non_creation":
                fixture.MakeFirstRecordNonCreation(lane);
                break;
            default:
                throw new InvalidOperationException(shape);
        }

        var result = fixture.Run();

        Assert.True(result.Success, result.Error);
        Assert.Equal("creation_unknown", ReasonFor(result.Output, lane));
    }

    /// <summary>
    /// **三种 reflog 首行形状都必须能解析出创建记录**(#3459)。
    ///
    /// 此前 `Probes.cs` 把「制表符在行末」当畸形而返回 `default` ⟹ 判 `creation_unknown` ⟹
    /// `worktree-clean` **永远回收不了那棵 lane**。而行末制表符只是**空 reflog message**,
    /// message 根本不参与解析(`record` 只取制表符之前的部分)。
    ///
    /// **这不是一个边角形状**:实测本机 127 棵有 `logs/HEAD` 的 worktree,
    /// **114 棵(89.8%)首行的制表符在行末**,11 棵无制表符,2 棵制表符在中间。
    /// 只测其中一种的话,今天新建的树(无制表符)恰好会让测试绿而 89.8% 的存量仍坏 ——
    /// 故本测试用 `[Theory]` 覆盖全部三形。
    /// </summary>
    [Theory]
    [InlineData("empty-message")]
    [InlineData("no-tab")]
    [InlineData("with-message")]
    public void EveryReflogFirstLineShapeYieldsACreationRecord(string shape)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/reflog-shape");
        switch (shape)
        {
            case "empty-message":
                fixture.MakeFirstRecordEmptyMessage(lane);
                break;
            case "no-tab":
                fixture.MakeFirstRecordWithoutTab(lane);
                break;
            case "with-message":
                break;
            default:
                throw new InvalidOperationException(shape);
        }

        var result = fixture.Run();

        Assert.True(result.Success, result.Error);
        Assert.NotEqual("creation_unknown", ReasonFor(result.Output, lane));
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
        Assert.Equal("merged_clean", ReasonFor(result.Output, unlocked));
    }

    [Fact]
    public void ClosedPrWhoseWorkLandedElsewhereIsRefused()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/closed-landed-elsewhere";
        var lane = fixture.AddLandedLane(branch);
        fixture.RegisterClosedPr(branch, fixture.Head(lane));

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("pr_not_merged", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void MergedPrMustMatchObservedHeadOid()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/pr-head-mismatch";
        var lane = fixture.AddLandedLane(branch);
        fixture.RegisterMergedPr(branch, new string('a', 40), fixture.Head(lane));

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("pr_not_merged", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void LiveProcessRefusesLaneWhileIdleControlIsReclaimed()
    {
        using var fixture = new CleanLanesFixture();
        var active = fixture.AddLandedLane("harness/active");
        var idle = fixture.AddLandedLane("harness/idle");
        fixture.MarkLaneInUse(active);

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(active));
        Assert.False(Directory.Exists(idle));
        Assert.Equal("in_use", ReasonFor(result.Output, active));
        Assert.Equal("merged_clean", ReasonFor(result.Output, idle));
    }

    [Fact]
    public void ProcessProbeFailureRefusesLane()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/process-unknown");
        fixture.FailProcessProbe(lane);

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("in_use_unknown", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void NewTermsDoNotChangeOrphanBranchOrTempJudgePaths()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/probe-refused");
        fixture.AddOrphan("harness/isolation-orphan", merged: true);
        var judge = fixture.AddDetachedJudge("trureturing-isolation-judge");

        var result = fixture.RunWithProbes(
            static (_, _, _) => new PullRequestProbeOutcome(false, []),
            static (_, _) => new LaneProcessProbeOutcome(false, false),
            "--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.False(fixture.BranchExists("harness/isolation-orphan"));
        Assert.False(Directory.Exists(judge));
        Assert.Equal("pr_unknown", ReasonFor(result.Output, lane));
        var items = ReadItems(result.Output);
        AssertItemProperty(items, "branch", "harness/isolation-orphan", "kind", "orphan_branch");
        AssertItemProperty(items, "path", judge, "kind", "temp_judge");
    }

    [Fact]
    public void DryRunAndForceAgreeOnEveryReason()
    {
        foreach (var reason in NewSkipReasons)
        {
            using var fixture = new CleanLanesFixture();
            var scenario = ArrangeReason(fixture, reason);

            var dryRun = fixture.RunAt(scenario.Now);
            var force = fixture.RunAt(scenario.Now, "--force");

            Assert.True(dryRun.Success, dryRun.Error);
            Assert.True(force.Success, force.Error);
            Assert.Equal(reason, ReasonFor(dryRun.Output, scenario.Path));
            Assert.Equal(reason, ReasonFor(force.Output, scenario.Path));
        }
    }

    [Theory]
    [InlineData("locked")]
    [InlineData("creation_unknown")]
    [InlineData("too_young")]
    [InlineData("age_unverifiable")]
    [InlineData("never_worked")]
    [InlineData("pr_not_merged")]
    [InlineData("pr_unknown")]
    [InlineData("in_use")]
    [InlineData("in_use_unknown")]
    public void EveryNewSkipReasonStringIsPinned(string reason)
    {
        using var fixture = new CleanLanesFixture();
        var scenario = ArrangeReason(fixture, reason);

        var result = fixture.RunAt(scenario.Now);

        Assert.True(result.Success, result.Error);
        Assert.Equal(reason, ReasonFor(result.Output, scenario.Path));
    }

    private static readonly string[] NewSkipReasons =
    [
        "locked",
        "creation_unknown",
        "too_young",
        "age_unverifiable",
        "never_worked",
        "pr_not_merged",
        "pr_unknown",
        "in_use",
        "in_use_unknown",
    ];

    private static (string Path, DateTimeOffset Now) ArrangeReason(
        CleanLanesFixture fixture,
        string reason)
    {
        var branch = $"harness/reason-{reason.Replace('_', '-')}";
        switch (reason)
        {
            case "locked":
            {
                var path = fixture.AddLandedLane(branch);
                fixture.LockLane(path);
                return (path, fixture.CreationTime(path).AddHours(48));
            }
            case "creation_unknown":
            {
                var path = fixture.AddLandedLane(branch);
                var now = fixture.CreationTime(path).AddHours(48);
                fixture.DeleteCreationLog(path);
                return (path, now);
            }
            case "too_young":
            {
                var path = fixture.AddLandedLane(branch);
                return (path, fixture.CreationTime(path).AddHours(23));
            }
            case "age_unverifiable":
            {
                var path = fixture.AddLandedLane(branch);
                return (path, fixture.CreationTime(path).AddSeconds(-1));
            }
            case "never_worked":
            {
                var path = fixture.AddMergedLane(branch);
                return (path, fixture.CreationTime(path).AddHours(48));
            }
            case "pr_not_merged":
            {
                var path = fixture.AddLandedLane(branch);
                fixture.RegisterClosedPr(branch, fixture.Head(path));
                return (path, fixture.CreationTime(path).AddHours(48));
            }
            case "pr_unknown":
            {
                var path = fixture.AddLandedLane(branch);
                fixture.FailPrProbe(branch);
                return (path, fixture.CreationTime(path).AddHours(48));
            }
            case "in_use":
            {
                var path = fixture.AddLandedLane(branch);
                fixture.MarkLaneInUse(path);
                return (path, fixture.CreationTime(path).AddHours(48));
            }
            case "in_use_unknown":
            {
                var path = fixture.AddLandedLane(branch);
                fixture.FailProcessProbe(path);
                return (path, fixture.CreationTime(path).AddHours(48));
            }
            default:
                throw new InvalidOperationException(reason);
        }
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

        private PullRequestProbeOutcome ProbePullRequests(
            string repositoryRoot,
            string branch,
            IWorktreeProcessRunner runner) =>
            pullRequests.TryGetValue(branch, out var outcome)
                ? outcome
                : new PullRequestProbeOutcome(true, []);

        private LaneProcessProbeOutcome ProbeLaneProcesses(
            string canonicalLanePath,
            IWorktreeProcessRunner runner) =>
            laneProcesses.TryGetValue(canonicalLanePath, out var outcome)
                ? outcome
                : new LaneProcessProbeOutcome(true, false);

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
