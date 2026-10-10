using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Runtime;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(1, false)]
    [InlineData(2, false)]
    [InlineData(3, false)]
    [InlineData(1, true)]
    [InlineData(2, true)]
    [InlineData(3, true)]
    public void CurrentHostActivityOrUnknownEvidenceRetainsAtEveryRefresh(int boundary, bool unknown)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/activity-refresh");
        fixture.LockLane(lane, InitializationLock);
        var reads = 0;
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (file != "python3" || args.LastOrDefault() != "active-paths") return null;
            if (++reads < boundary) return new ProcessOutput(0, Encoding.UTF8.GetBytes("[]"), []);
            return unknown ? GitFailure("activity unavailable")
                : new ProcessOutput(0, Encoding.UTF8.GetBytes(JsonSerializer.Serialize(new[] { lane })), []);
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal(unknown ? "locked_activity_unknown" : "locked_activity", ReasonFor(result.Output, lane));
        Assert.Equal(boundary, reads);
        Assert.Equal(InitializationLock,
            File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
        Assert.DoesNotContain(runner.Invocations, call => call.Arguments.Take(2).SequenceEqual(["worktree", "remove"]));
    }

    [Theory]
    [InlineData("identity", "identity_changed")]
    [InlineData("content", "content_changed")]
    [InlineData("staged", "evidence_changed")]
    [InlineData("history", "history_changed")]
    [InlineData("branch-history", "history_changed")]
    [InlineData("private-recovery", "history_changed")]
    [InlineData("nested", "nested_worktree")]
    [InlineData("manual-lock", "locked_changed")]
    [InlineData("inventory-failure", "unreadable")]
    [InlineData("relocation", "locked_changed")]
    public void FinalLockedObservationDriftRefusesRemoval(string change, string reason)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/final-locked-refresh");
        fixture.LockLane(lane, InitializationLock);
        var moved = lane + "-moved";
        var inventories = 0;
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (file != "git" || !args.SequenceEqual(["worktree", "list", "--porcelain", "-z"])
                || ++inventories != 3) return null;
            switch (change)
            {
                case "identity":
                    CleanLanesFixture.Git(lane, "switch", "-c", "scratch/replacement");
                    File.WriteAllText(Path.Combine(lane, "new.txt"), "resumed session\n");
                    break;
                case "content":
                    File.WriteAllText(Path.Combine(lane, "new.txt"), "new content\n");
                    break;
                case "staged":
                    File.AppendAllText(Path.Combine(lane, "README.md"), "new staging\n");
                    CleanLanesFixture.Git(lane, "add", "README.md");
                    CleanLanesFixture.Git(lane, "restore", "--source=HEAD", "--worktree", "README.md");
                    break;
                case "history":
                    var log = Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD");
                    File.AppendAllText(log, File.ReadLines(log).Last() + "\n");
                    break;
                case "branch-history":
                    var branchLog = CleanLanesFixture.Git(lane, "rev-parse", "--path-format=absolute",
                        "--git-path", "logs/refs/heads/harness/final-locked-refresh").Trim();
                    File.AppendAllText(branchLog, File.ReadLines(branchLog).Last() + "\n");
                    break;
                case "private-recovery":
                    File.WriteAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "ORIG_HEAD"),
                        fixture.Head(lane) + "\n");
                    break;
                case "nested":
                    fixture.AddNestedWorktree(lane);
                    break;
                case "manual-lock":
                    CleanLanesFixture.Git(lane, "worktree", "unlock", lane);
                    fixture.LockLane(lane, "intentional resumed session");
                    break;
                case "relocation":
                    CleanLanesFixture.Git(lane, "worktree", "move", "--force", "--force", lane, moved);
                    break;
                case "inventory-failure": return GitFailure("final locked inventory unavailable");
            }
            return null;
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        var retained = change == "relocation" ? moved : lane;
        Assert.True(Directory.Exists(retained));
        Assert.Equal(reason, ReasonFor(result.Output, lane));
        Assert.DoesNotContain(runner.Invocations, call => call.Arguments.Take(2).SequenceEqual(["worktree", "remove"]));
        Assert.Equal(change == "manual-lock" ? "intentional resumed session" : InitializationLock,
            File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(retained), "locked")).Trim());
        Assert.DoesNotContain(runner.Invocations, call => call.Arguments.Take(2).SequenceEqual(["worktree", "unlock"]));
    }

    [Theory]
    [InlineData("before-native")]
    [InlineData("native-refusal")]
    [InlineData("after-native")]
    public void LockedNativeRemovalFailureReportsPartialWithoutUnlocking(string boundary)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/locked-remove-failure");
        fixture.LockLane(lane, InitializationLock);
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((file, args, cwd) =>
        {
            if (file != "python3" || !IsProtocol(args, "remove")) return null;
            Assert.Contains("--initialization", args);
            Assert.Equal(lane, ProtocolValue(args, "--path"));
            Assert.Equal(InitializationLock,
                File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
            if (boundary == "native-refusal")
            {
                var refused = production.Run("git", ["worktree", "remove", "--force", "--", lane],
                    cwd, TestBudgets.ScriptProcessHangGuard);
                Assert.NotEqual(0, refused.ExitCode);
                return refused;
            }
            if (boundary == "after-native")
                Assert.Equal(0, production.Run(file, args, cwd, TestBudgets.ScriptProcessHangGuard).ExitCode);
            return GitFailure("returned removal failure");
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.False(result.Success);
        Assert.Equal(boundary != "after-native", Directory.Exists(lane));
        Assert.Equal("worktree_remove_failed_state_indeterminate", ReasonFor(result.Output, lane));
        Assert.Equal(1, ReadSummary(result.Output).GetProperty("partial_count").GetInt32());
        Assert.True(fixture.BranchExists("harness/locked-remove-failure"));
        if (boundary != "after-native")
            Assert.Equal(InitializationLock,
                File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
        Assert.DoesNotContain(runner.Invocations, call => call.Arguments.Take(2).SequenceEqual(["worktree", "unlock"])
            || call.Arguments.Take(2).SequenceEqual(["worktree", "lock"]));
    }

    [Theory]
    [InlineData("branch-read")]
    [InlineData("first-inventory")]
    [InlineData("final-inventory")]
    [InlineData("initial-metadata")]
    [InlineData("first-metadata")]
    [InlineData("final-metadata")]
    [InlineData("first-inventory-unavailable")]
    [InlineData("final-inventory-unavailable")]
    [InlineData("initial-activity-unavailable")]
    [InlineData("first-activity-unavailable")]
    [InlineData("final-activity-unavailable")]
    [InlineData("head-unavailable")]
    [InlineData("branch-unavailable")]
    public void FullCleanupRetainsManagedBranchObservedDuringLockedRefusal(string boundary)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/full-locked-refresh");
        var laneHead = fixture.Head(lane);
        fixture.LockLane(lane, InitializationLock);
        const string replacement = "lane/governance/resumed";
        const string orphan = "harness/full-orphan-control";
        fixture.AddOrphan(orphan, merged: true);
        var snapshot = fixture.AddGitlessJudgeSnapshot("trureturing-full-snapshot-control");
        var inventories = 0;
        var commonReads = 0;
        var activityReads = 0;
        var switched = false;
        string? registered = null;
        var runner = fixture.CreateRunner((file, args, cwd) =>
        {
            var activity = file == "python3" && args.LastOrDefault() == "active-paths";
            var inventory = file == "git" && args.SequenceEqual(["worktree", "list", "--porcelain", "-z"]);
            var common = file == "git" && args.SequenceEqual(["rev-parse", "--git-common-dir"]);
            if (inventory) inventories++;
            if (common) commonReads++;
            if (activity) activityReads++;
            var trigger = boundary switch
            {
                "initial-metadata" or "initial-activity-unavailable" => activity && activityReads == 1,
                "first-metadata" => common && commonReads == 2,
                "final-metadata" => common && commonReads == 4,
                "first-inventory-unavailable" => inventory && inventories == 2,
                "final-inventory-unavailable" => inventory && inventories == 3,
                "first-activity-unavailable" => activity && activityReads == 2,
                "final-activity-unavailable" => activity && activityReads == 3,
                "head-unavailable" => file == "git" && cwd == lane
                    && args.SequenceEqual(["rev-parse", "--verify", "HEAD^{commit}"]),
                "branch-unavailable" => file == "git" && cwd == lane
                    && args.SequenceEqual(["branch", "--show-current"]),
                _ => file == "git" && (boundary == "branch-read" && cwd == lane
                    && args.SequenceEqual(["branch", "--show-current"])
                || inventory && inventories == (boundary == "first-inventory" ? 2 : 3)
                    && boundary != "branch-read"),
            };
            if (!switched && trigger)
            {
                CleanLanesFixture.Git(lane, "switch", "-c", replacement);
                registered = CleanLanesFixture.Git(
                    fixture.AddAttachedTempDirectory("trureturing-fresh-registration"),
                    "rev-parse", "--show-toplevel").Trim();
                CleanLanesFixture.Git(registered, "switch", "-c", "lane/governance/fresh-registration");
                fixture.LockLane(registered, InitializationLock);
                File.WriteAllText(Path.Combine(registered, "unsaved.txt"), "fresh unsaved material\n");
                switched = true;
                if (boundary.EndsWith("unavailable", StringComparison.Ordinal))
                    return GitFailure("controlled unavailable observation");
            }
            return null;
        });
        var result = fixture.RunWithRaw(runner, "--force");
        Assert.True(switched);
        Assert.True(result.Success, result.Error);
        Assert.Equal(boundary switch
            {
                "final-inventory" => "identity_changed",
                "initial-metadata" => "locked_evidence",
                "first-metadata" or "final-metadata" => "evidence_changed",
                "initial-activity-unavailable" or "first-activity-unavailable"
                    or "final-activity-unavailable" => "locked_activity_unknown",
                _ => "unreadable",
            },
            ReasonFor(result.Output, lane));
        Assert.True(Directory.Exists(lane));
        Assert.True(fixture.WorktreeRegistered(lane));
        Assert.True(fixture.BranchExists(replacement));
        Assert.Equal(laneHead, fixture.Head(lane));
        Assert.Equal(replacement, CleanLanesFixture.Git(lane, "branch", "--show-current").Trim());
        Assert.Equal(InitializationLock,
            File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
        Assert.DoesNotContain(runner.Invocations, call => call.Arguments.Take(2).SequenceEqual(["worktree", "remove"])
            || call.Arguments.Contains($"refs/heads/{replacement}"));
        Assert.True(fixture.BranchExists(orphan));
        Assert.True(Directory.Exists(snapshot));
        Assert.NotNull(registered);
        Assert.True(Directory.Exists(registered));
        Assert.True(fixture.WorktreeRegistered(registered));
        Assert.True(fixture.BranchExists("lane/governance/fresh-registration"));
        Assert.NotEmpty(fixture.Head(registered));
        Assert.Equal(InitializationLock,
            File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(registered), "locked")).Trim());
        Assert.Equal("fresh unsaved material\n", File.ReadAllText(Path.Combine(registered, "unsaved.txt")));
        AssertExtraSweepsDeferred(result, runner);
        Console.WriteLine($"full cleanup: boundary={boundary} native refs/HEAD/trees/locks/unsaved registration retained; extra sweeps deferred");
    }

    private static void AssertExtraSweepsDeferred(CommandResult result, ScriptedWorktreeProcessRunner runner)
    {
        var summary = ReadSummary(result.Output);
        Assert.Equal("full", summary.GetProperty("scope").GetString());
        Assert.Equal("deferred", summary.GetProperty("extra_sweeps").GetString());
        Assert.Equal("lane_preservation_unresolved", summary.GetProperty("extra_sweeps_reason").GetString());
        Assert.DoesNotContain(ReadItems(result.Output), item =>
            item.GetProperty("kind").GetString() is "orphan_branch" or "temp_judge");
        Assert.DoesNotContain(runner.Invocations, call => call.Arguments.SequenceEqual(
            ["for-each-ref", "--format=%(refname:short)", "refs/heads"]));
    }

    [Theory]
    [InlineData("intentional", false)]
    [InlineData("intentional", true)]
    [InlineData("unknown", false)]
    [InlineData("unknown", true)]
    [InlineData("missing", false)]
    [InlineData("missing", true)]
    [InlineData("marker", false)]
    [InlineData("marker", true)]
    [InlineData("git-directory", false)]
    [InlineData("git-directory", true)]
    [InlineData("nested", false)]
    [InlineData("nested", true)]
    public void EarlyLockedRetentionDefersBothFullSweeps(string disposition, bool force)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/early-retained";
        var lane = fixture.AddLandedLane(branch);
        var head = fixture.Head(lane);
        fixture.LockLane(lane, disposition == "intentional" ? "intentional retention"
            : disposition == "unknown" ? "worktree-init:invalid" : InitializationLock);
        var administration = fixture.WorktreeGitDirectory(lane);
        var lockBytes = File.ReadAllBytes(Path.Combine(administration, "locked"));
        var retainedPath = lane;
        if (disposition == "missing")
        {
            retainedPath = lane + "-offline";
            Directory.Move(lane, retainedPath);
        }
        if (disposition == "marker") File.Delete(Path.Combine(lane, ".git"));
        if (disposition == "nested") fixture.AddNestedWorktree(lane);
        fixture.AddOrphan("harness/early-orphan-control", merged: true);
        var snapshot = fixture.AddGitlessJudgeSnapshot("trureturing-early-snapshot-control");
        var runner = fixture.CreateRunner((file, args, cwd) =>
            disposition == "git-directory" && file == "git" && cwd == lane
                && args.Contains("--absolute-git-dir") ? GitFailure("unavailable administration") : null);
        var result = fixture.RunWithRaw(runner, force ? ["--force"] : []);
        Assert.True(result.Success, result.Error);
        Assert.Equal(disposition switch
        {
            "intentional" => "locked_intentional",
            "unknown" => "locked_unknown",
            "missing" => "missing",
            "nested" => "nested_worktree",
            _ => "unreadable",
        }, ReasonFor(result.Output, lane));
        Assert.True(Directory.Exists(retainedPath));
        Assert.Equal(lockBytes, File.ReadAllBytes(Path.Combine(administration, "locked")));
        Assert.True(fixture.BranchExists(branch));
        if (disposition is not ("missing" or "marker")) Assert.Equal(head, fixture.Head(lane));
        Assert.True(fixture.BranchExists("harness/early-orphan-control"));
        Assert.True(Directory.Exists(snapshot));
        AssertExtraSweepsDeferred(result, runner);
    }

    [Fact]
    public void InvokingLockedWorktreeDefersFullSweepsBeforeProbing()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/current-locked";
        var lane = fixture.AddLandedLane(branch);
        fixture.LockLane(lane, InitializationLock);
        var head = fixture.Head(lane);
        fixture.AddOrphan("harness/current-orphan-control", merged: true);
        var snapshot = fixture.AddGitlessJudgeSnapshot("trureturing-current-snapshot-control");
        var runner = fixture.CreateRunner();
        var result = CleanLanesCommand.Run(lane, ["--base", "dev", "--force"], runner,
            [fixture.OwnedWorkingDirectory(CleanLanesFixture.OwnedDirectory.Temporary)],
            new DateTimeOffset(2030, 1, 2, 0, 0, 0, TimeSpan.Zero));
        Assert.True(result.Success, result.Error);
        Assert.Equal("current", ReasonFor(result.Output, lane));
        Assert.Equal(head, fixture.Head(lane));
        Assert.Equal(InitializationLock,
            File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
        Assert.True(fixture.BranchExists(branch));
        Assert.True(fixture.BranchExists("harness/current-orphan-control"));
        Assert.True(Directory.Exists(snapshot));
        AssertExtraSweepsDeferred(result, runner);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FreshLockedRegistrationDuringUnlockedRemovalDefersFullSweeps(bool lockSubject)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/unlocked-initial-subject";
        var lane = fixture.AddLandedLane(branch);
        var head = fixture.Head(lane);
        fixture.AddOrphan("harness/fresh-orphan-control", merged: true);
        var snapshot = fixture.AddGitlessJudgeSnapshot("trureturing-fresh-snapshot-control");
        var inventories = 0;
        string? fresh = null;
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (file != "git" || !args.SequenceEqual(["worktree", "list", "--porcelain", "-z"])
                || ++inventories != 2) return null;
            fresh = CleanLanesFixture.Git(fixture.AddAttachedTempDirectory("trureturing-fresh-locked"),
                "rev-parse", "--show-toplevel").Trim();
            CleanLanesFixture.Git(fresh, "switch", "-c", "lane/governance/fresh-locked");
            fixture.LockLane(fresh, InitializationLock);
            File.WriteAllText(Path.Combine(fresh, "unsaved.txt"), "unsaved registration\n");
            if (lockSubject) fixture.LockLane(lane, InitializationLock);
            return null;
        });
        var result = fixture.RunWithRaw(runner, "--force");
        Assert.True(result.Success, result.Error);
        Assert.NotNull(fresh);
        Assert.True(Directory.Exists(fresh));
        Assert.True(fixture.WorktreeRegistered(fresh));
        Assert.True(fixture.BranchExists("lane/governance/fresh-locked"));
        Assert.NotEmpty(fixture.Head(fresh));
        Assert.Equal(InitializationLock,
            File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(fresh), "locked")).Trim());
        Assert.Equal("unsaved registration\n", File.ReadAllText(Path.Combine(fresh, "unsaved.txt")));
        Assert.Equal(lockSubject, Directory.Exists(lane));
        Assert.Equal(lockSubject, fixture.BranchExists(branch));
        if (lockSubject)
        {
            Assert.Equal("locked", ReasonFor(result.Output, lane));
            Assert.Equal(head, fixture.Head(lane));
            Assert.Equal(InitializationLock,
                File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
        }
        Assert.True(fixture.BranchExists("harness/fresh-orphan-control"));
        Assert.True(Directory.Exists(snapshot));
        AssertExtraSweepsDeferred(result, runner);
    }

    [Theory]
    [InlineData("before-native")]
    [InlineData("native-refusal")]
    [InlineData("after-native")]
    [InlineData("branch-ref")]
    public void IncompleteLockedRemovalDefersFullSweeps(string boundary)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/incomplete-locked";
        var lane = fixture.AddLandedLane(branch);
        fixture.LockLane(lane, InitializationLock);
        fixture.AddOrphan("harness/incomplete-orphan-control", merged: true);
        var snapshot = fixture.AddGitlessJudgeSnapshot("trureturing-incomplete-snapshot-control");
        var native = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((file, args, cwd) =>
        {
            if (file != "python3") return null;
            if (boundary == "branch-ref" && IsProtocol(args, "retire-branch")
                && args.Contains(branch)) return GitFailure("controlled ref refusal");
            if (boundary == "branch-ref" || !IsProtocol(args, "remove")) return null;
            if (boundary == "native-refusal")
            {
                var refused = native.Run("git", ["worktree", "remove", "--force", "--", lane],
                    cwd, TestBudgets.ScriptProcessHangGuard);
                Assert.NotEqual(0, refused.ExitCode);
                return refused;
            }
            if (boundary == "after-native")
                Assert.Equal(0, native.Run(file, args, cwd, TestBudgets.ScriptProcessHangGuard).ExitCode);
            return GitFailure("controlled indeterminate removal");
        });
        var result = fixture.RunWithRaw(runner, "--force");
        Assert.False(result.Success);
        Assert.Equal(1, ReadSummary(result.Output).GetProperty("partial_count").GetInt32());
        Assert.Equal(boundary is "before-native" or "native-refusal", Directory.Exists(lane));
        Assert.True(fixture.BranchExists(branch));
        if (Directory.Exists(lane))
        {
            Assert.NotEmpty(fixture.Head(lane));
            Assert.Equal(InitializationLock,
                File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
        }
        Assert.True(fixture.BranchExists("harness/incomplete-orphan-control"));
        Assert.True(Directory.Exists(snapshot));
        AssertExtraSweepsDeferred(result, runner);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void UnrelatedSuccessfulRemovalCannotClearLockedPreservation(bool retainedFirst)
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane(retainedFirst
            ? "harness/retained-subject-with-longer-path" : "harness/retained");
        fixture.LockLane(retained, InitializationLock);
        File.WriteAllText(Path.Combine(retained, "unsaved.txt"), "retained unsaved work\n");
        var removed = fixture.AddLandedLane(retainedFirst
            ? "harness/idle" : "harness/idle-subject-with-longer-path");
        fixture.LockLane(removed, InitializationLock);
        fixture.AddOrphan("harness/order-orphan-control", merged: true);
        var snapshot = fixture.AddGitlessJudgeSnapshot("trureturing-order-snapshot-control");
        var runner = fixture.CreateRunner();
        var result = fixture.RunWithRaw(runner, "--force");
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(retained));
        Assert.NotEmpty(fixture.Head(retained));
        Assert.Equal("retained unsaved work\n", File.ReadAllText(Path.Combine(retained, "unsaved.txt")));
        Assert.Equal(InitializationLock,
            File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(retained), "locked")).Trim());
        Assert.False(Directory.Exists(removed));
        Assert.True(fixture.BranchExists("harness/order-orphan-control"));
        Assert.True(Directory.Exists(snapshot));
        AssertExtraSweepsDeferred(result, runner);
    }

    [Fact]
    public void IdleFullInvocationReclaimsLaneOrphanAndTemporaryControls()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/full-idle";
        var lane = fixture.AddLandedLane(branch);
        fixture.LockLane(lane, InitializationLock);
        fixture.AddOrphan("harness/idle-orphan-control", merged: true);
        var snapshot = fixture.AddGitlessJudgeSnapshot("trureturing-idle-snapshot-control");
        var pointer = fixture.AddOrphanTempDirectory("trureturing-idle-pointer-control");
        var runner = fixture.CreateRunner();
        var preview = fixture.RunWithRaw(runner);
        Assert.True(preview.Success, preview.Error);
        AssertExtraSweepsDeferred(preview, runner);
        Assert.Equal("stale_initialization_lock", ReasonFor(preview.Output, lane));
        Assert.True(Directory.Exists(lane));
        runner = fixture.CreateRunner();
        var result = fixture.RunWithRaw(runner, "--force");
        Assert.True(result.Success, result.Error + result.Output);
        Assert.False(Directory.Exists(lane));
        Assert.False(fixture.WorktreeRegistered(lane));
        Assert.False(fixture.BranchExists(branch));
        Assert.False(fixture.BranchExists("harness/idle-orphan-control"));
        Assert.False(Directory.Exists(snapshot));
        Assert.True(Directory.Exists(pointer));
        Assert.Contains("gitdir:", File.ReadAllText(Path.Combine(pointer, ".git")), StringComparison.Ordinal);
        Assert.Equal("completed", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
        Assert.Equal(JsonValueKind.Null, ReadSummary(result.Output).GetProperty("extra_sweeps_reason").ValueKind);
    }
}
