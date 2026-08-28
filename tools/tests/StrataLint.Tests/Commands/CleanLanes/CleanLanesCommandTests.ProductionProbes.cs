using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData("success", "merged_clean")]
    [InlineData("empty", "pr_unknown")]
    [InlineData("malformed", "pr_unknown")]
    [InlineData("nonzero", "pr_unknown")]
    public void ProductionPrAdapterClassifiesScriptedOutcomes(
        string outcome,
        string expectedReason)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/production-pr-adapter";
        var lane = fixture.AddLandedLane(branch);
        var head = fixture.Head(lane);
        var runner = fixture.CreateRunner((fileName, _, _) => fileName switch
        {
            "gh" => outcome switch
            {
                "success" => SuccessfulPrOutput(branch, head),
                "empty" => new ProcessOutput(0, [], []),
                "malformed" => new ProcessOutput(0, Encoding.UTF8.GetBytes("{}\n"), []),
                "nonzero" => new ProcessOutput(1, [], Encoding.UTF8.GetBytes("gh failed\n")),
                _ => throw new InvalidOperationException(outcome),
            },
            "lsof" => IdleLsofOutput(),
            _ => null,
        });

        var result = fixture.RunWithProductionProbes(runner);

        Assert.True(result.Success, result.Error);
        Assert.Equal(expectedReason, ReasonFor(result.Output, lane));
        AssertGhInvocation(runner.Invocations, branch, fixture.RepositoryWorkingDirectory);
        AssertLsofInvocations(runner.Invocations, outcome == "success" ? 1 : 0);
    }

    [Theory]
    [InlineData("success", "merged_clean")]
    [InlineData("hit", "in_use")]
    [InlineData("empty", "in_use_unknown")]
    [InlineData("malformed", "in_use_unknown")]
    [InlineData("nonzero", "in_use_unknown")]
    public void ProductionProcessAdapterClassifiesScriptedOutcomes(
        string outcome,
        string expectedReason)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/production-process-adapter";
        var lane = fixture.AddLandedLane(branch);
        var head = fixture.Head(lane);
        var runner = fixture.CreateRunner((fileName, _, _) => fileName switch
        {
            "gh" => SuccessfulPrOutput(branch, head),
            "lsof" => outcome switch
            {
                "success" => IdleLsofOutput(),
                "hit" => LsofOutput(lane),
                "empty" => new ProcessOutput(0, [], []),
                "malformed" => new ProcessOutput(
                    0,
                    Encoding.UTF8.GetBytes("p123\0fcwd\0"),
                    []),
                "nonzero" => new ProcessOutput(
                    1,
                    [],
                    Encoding.UTF8.GetBytes("lsof failed\n")),
                _ => throw new InvalidOperationException(outcome),
            },
            _ => null,
        });

        var result = fixture.RunWithProductionProbes(runner);

        Assert.True(result.Success, result.Error);
        Assert.Equal(expectedReason, ReasonFor(result.Output, lane));
        AssertGhInvocation(runner.Invocations, branch, fixture.RepositoryWorkingDirectory);
        AssertLsofInvocations(runner.Invocations, 1);
    }

    [Fact]
    public void ProductionEvaluationPathInstallsPrAndProcessAdapters()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/production-wiring";
        var lane = fixture.AddLandedLane(branch);
        var head = fixture.Head(lane);
        var runner = fixture.CreateRunner((fileName, _, _) => fileName switch
        {
            "gh" => SuccessfulPrOutput(branch, head),
            "lsof" => IdleLsofOutput(),
            _ => null,
        });

        var result = fixture.RunWithProductionProbes(runner, "--force");

        Assert.True(result.Success, result.Error);
        Assert.Equal("merged_clean", ReasonFor(result.Output, lane));
        AssertGhInvocation(runner.Invocations, branch, fixture.RepositoryWorkingDirectory);
        AssertLsofInvocations(runner.Invocations, 2);
    }

    [Fact]
    public void ForceRetainsLaneAndContinuesWhenHeadRereadFails()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/head-reread-a-failure");
        var removed = fixture.AddLandedLane("harness/head-reread-z-control");
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
            IsLaneGit(
                fileName,
                arguments,
                workingDirectory,
                retained,
                "rev-parse",
                "--verify",
                "HEAD^{commit}")
                ? GitFailure("head reread failed")
                : null);

        var result = fixture.RunWithRaw(runner, "--force");

        AssertRetainedAndControlReclaimed(result, retained, removed, "unreadable");
    }

    [Fact]
    public void ForceRetainsLaneAndContinuesWhenBranchRereadFails()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/branch-reread-a-failure");
        var removed = fixture.AddLandedLane("harness/branch-reread-z-control");
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
            IsLaneGit(
                fileName,
                arguments,
                workingDirectory,
                retained,
                "branch",
                "--show-current")
                ? GitFailure("branch reread failed")
                : null);

        var result = fixture.RunWithRaw(runner, "--force");

        AssertRetainedAndControlReclaimed(result, retained, removed, "unreadable");
    }

    [Fact]
    public void ForceRetainsLaneAndContinuesWhenIdentityDriftsBeforeFinalStatus()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/identity-drift-a-failure");
        var removed = fixture.AddLandedLane("harness/identity-drift-z-control");
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
            IsLaneGit(
                fileName,
                arguments,
                workingDirectory,
                retained,
                "rev-parse",
                "--verify",
                "HEAD^{commit}")
                ? new ProcessOutput(
                    0,
                    Encoding.UTF8.GetBytes(new string('0', 40) + "\n"),
                    [])
                : null);

        var result = fixture.RunWithRaw(runner, "--force");

        AssertRetainedAndControlReclaimed(result, retained, removed, "unreadable");
    }

    [Fact]
    public void ForceRetainsLaneAndContinuesWhenBranchDriftsBeforeFinalStatus()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/branch-drift-a-failure");
        var removed = fixture.AddLandedLane("harness/branch-drift-z-control");
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
            IsLaneGit(
                fileName,
                arguments,
                workingDirectory,
                retained,
                "branch",
                "--show-current")
                ? new ProcessOutput(
                    0,
                    Encoding.UTF8.GetBytes("harness/replacement-branch\n"),
                    [])
                : null);

        var result = fixture.RunWithRaw(runner, "--force");

        AssertRetainedAndControlReclaimed(result, retained, removed, "unreadable");
    }

    [Fact]
    public void ForceRetainsLaneAndContinuesWhenFinalStatusRereadFails()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/status-reread-a-failure");
        var removed = fixture.AddLandedLane("harness/status-reread-z-control");
        var statusCalls = 0;
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
        {
            if (!IsLaneGit(
                    fileName,
                    arguments,
                    workingDirectory,
                    retained,
                    "status",
                    "--porcelain=v1",
                    "-z",
                    "--untracked-files=all"))
            {
                return null;
            }

            statusCalls++;
            return statusCalls == 2 ? GitFailure("status reread failed") : null;
        });

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.Equal(2, statusCalls);
        AssertRetainedAndControlReclaimed(result, retained, removed, "unreadable");
    }

    [Fact]
    public void ForceRetainsLaneAndContinuesWhenLaneBecomesDirtyBeforeRemoval()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/dirty-drift-a-failure");
        var removed = fixture.AddLandedLane("harness/dirty-drift-z-control");
        var statusCalls = 0;
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
        {
            if (!IsLaneGit(
                    fileName,
                    arguments,
                    workingDirectory,
                    retained,
                    "status",
                    "--porcelain=v1",
                    "-z",
                    "--untracked-files=all"))
            {
                return null;
            }

            statusCalls++;
            return statusCalls == 2
                ? new ProcessOutput(
                    0,
                    Encoding.UTF8.GetBytes("?? late-dirty.txt\0"),
                    [])
                : null;
        });

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.Equal(2, statusCalls);
        AssertRetainedAndControlReclaimed(result, retained, removed, "dirty");
    }

    [Fact]
    public void ForceRetainsLaneAndContinuesWhenRefreshedIdentityChanges()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/refresh-identity-a-failure");
        var removed = fixture.AddLandedLane("harness/refresh-identity-z-control");
        var retainedHead = fixture.Head(retained);
        var replacementHead = fixture.Head(removed);
        var inventoryCalls = 0;
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
        {
            if (fileName != "git"
                || !arguments.SequenceEqual(["worktree", "list", "--porcelain", "-z"]))
            {
                return null;
            }

            inventoryCalls++;
            if (inventoryCalls != 2) return null;

            var output = production.Run(
                fileName,
                arguments,
                workingDirectory,
                BoundedProcessRunner.HangDetectionBudget);
            var inventory = Encoding.UTF8.GetString(output.StandardOutput);
            var observedRecord = $"worktree {retained}\0HEAD {retainedHead}\0";
            var changedRecord = $"worktree {retained}\0HEAD {replacementHead}\0";
            return new ProcessOutput(
                output.ExitCode,
                Encoding.UTF8.GetBytes(inventory.Replace(
                    observedRecord,
                    changedRecord,
                    StringComparison.Ordinal)),
                output.StandardError);
        });

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.Equal(3, inventoryCalls);
        AssertRetainedAndControlReclaimed(result, retained, removed, "unreadable");
    }

    [Fact]
    public void ForceRetainsLaneAndContinuesWhenRefreshedBranchChanges()
    {
        using var fixture = new CleanLanesFixture();
        const string retainedBranch = "harness/refresh-branch-a-failure";
        var retained = fixture.AddLandedLane(retainedBranch);
        var removed = fixture.AddLandedLane("harness/refresh-branch-z-control");
        var retainedHead = fixture.Head(retained);
        var inventoryCalls = 0;
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
        {
            if (fileName != "git"
                || !arguments.SequenceEqual(["worktree", "list", "--porcelain", "-z"]))
            {
                return null;
            }

            inventoryCalls++;
            if (inventoryCalls != 2) return null;

            var output = production.Run(
                fileName,
                arguments,
                workingDirectory,
                BoundedProcessRunner.HangDetectionBudget);
            var inventory = Encoding.UTF8.GetString(output.StandardOutput);
            var observedRecord = $"worktree {retained}\0HEAD {retainedHead}\0"
                + $"branch refs/heads/{retainedBranch}\0";
            var changedRecord = $"worktree {retained}\0HEAD {retainedHead}\0"
                + "branch refs/heads/harness/replacement-branch\0";
            return new ProcessOutput(
                output.ExitCode,
                Encoding.UTF8.GetBytes(inventory.Replace(
                    observedRecord,
                    changedRecord,
                    StringComparison.Ordinal)),
                output.StandardError);
        });

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.Equal(3, inventoryCalls);
        AssertRetainedAndControlReclaimed(result, retained, removed, "unreadable");
    }

    [Fact]
    public void ForceReportsIndeterminatePartialWhenGitFailsAfterDestructiveSideEffects()
    {
        using var fixture = new CleanLanesFixture();
        const string damagedBranch = "harness/remove-destructive-a-partial";
        const string removedBranch = "harness/remove-destructive-z-control";
        var damaged = fixture.AddLandedLane(damagedBranch);
        var removed = fixture.AddLandedLane(removedBranch);
        var damagedHead = fixture.Head(damaged);
        var retainedTrackedFile = Path.Combine(damaged, "README.md");
        var deletedTrackedFile = Path.Combine(
            damaged,
            damagedBranch.Replace('/', '-') + ".txt");
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
        {
            if (fileName != "git"
                || !arguments.SequenceEqual(["worktree", "remove", damaged]))
            {
                return null;
            }

            var removal = production.Run(
                fileName,
                arguments,
                workingDirectory,
                BoundedProcessRunner.HangDetectionBudget);
            Assert.Equal(0, removal.ExitCode);
            Assert.False(fixture.WorktreeRegistered(damaged));
            Directory.CreateDirectory(damaged);
            File.WriteAllText(
                retainedTrackedFile,
                "# clean lanes fixture\n",
                new UTF8Encoding(false));
            return new ProcessOutput(
                255,
                removal.StandardOutput,
                Encoding.UTF8.GetBytes("synthetic failure after destructive removal\n"));
        });

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.False(result.Success);
        Assert.Equal("CLEAN_LANES_PARTIAL_FAILURE count=1\n", result.Error);
        Assert.False(fixture.WorktreeRegistered(damaged));
        Assert.True(Directory.Exists(damaged));
        Assert.True(File.Exists(retainedTrackedFile));
        Assert.False(File.Exists(deletedTrackedFile));
        Assert.True(fixture.BranchExists(damagedBranch));
        Assert.False(Directory.Exists(removed));
        Assert.False(fixture.BranchExists(removedBranch));
        var items = ReadItems(result.Output);
        AssertPartialItem(
            items,
            damaged,
            damagedBranch,
            damagedHead,
            "worktree_remove_failed_state_indeterminate");
        Assert.Contains(items, item =>
            ItemMatches(item, removed, "removed", "merged_clean"));
        var summary = ReadSummary(result.Output);
        Assert.Equal(1, summary.GetProperty("partial_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removable_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removed_count").GetInt32());
    }

    [Fact]
    public void ForceReportsPartialRemovalAndReclaimsHealthyLaneWhenBranchDeletionFails()
    {
        using var fixture = new CleanLanesFixture();
        const string retainedBranch = "harness/ref-delete-a-partial";
        const string removedBranch = "harness/ref-delete-z-control";
        var partial = fixture.AddLandedLane(retainedBranch);
        var removed = fixture.AddLandedLane(removedBranch);
        var retainedHead = fixture.Head(partial);
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
            fileName == "git"
            && arguments.Count > 2
            && arguments[0] == "update-ref"
            && arguments[1] == "-d"
            && arguments[2] == $"refs/heads/{retainedBranch}"
                ? GitFailure("synthetic branch deletion failure")
                : null);

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.False(result.Success);
        Assert.Equal("CLEAN_LANES_PARTIAL_FAILURE count=1\n", result.Error);
        Assert.False(Directory.Exists(partial));
        Assert.True(fixture.BranchExists(retainedBranch));
        Assert.False(Directory.Exists(removed));
        Assert.False(fixture.BranchExists(removedBranch));
        var items = ReadItems(result.Output);
        AssertPartialItem(items, partial, retainedBranch, retainedHead, "branch_ref_retained");
        Assert.Contains(items, item =>
            ItemMatches(item, removed, "removed", "merged_clean"));
        Assert.Contains("\"event\":\"clean_lanes_summary\"", result.Output, StringComparison.Ordinal);
        var summary = ReadSummary(result.Output);
        Assert.Equal(1, summary.GetProperty("partial_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removable_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removed_count").GetInt32());
    }

    [Fact]
    public void ForceReportsExactCountForTwoRetainedBranchRefsAndReclaimsHealthyControl()
    {
        using var fixture = new CleanLanesFixture();
        string[] partialBranches =
        [
            "harness/ref-delete-a-partial",
            "harness/ref-delete-b-partial",
        ];
        var partials = partialBranches.Select(branch => fixture.AddLandedLane(branch)).ToArray();
        const string removedBranch = "harness/ref-delete-z-control";
        var removed = fixture.AddLandedLane(removedBranch);
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
            fileName == "git"
            && arguments.Count > 2
            && arguments[0] == "update-ref"
            && arguments[1] == "-d"
            && partialBranches.Contains(
                arguments[2]["refs/heads/".Length..],
                StringComparer.Ordinal)
                ? GitFailure("synthetic branch deletion failure")
                : null);

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.False(result.Success);
        Assert.Equal("CLEAN_LANES_PARTIAL_FAILURE count=2\n", result.Error);
        Assert.All(partials, path => Assert.False(Directory.Exists(path)));
        Assert.All(partialBranches, branch => Assert.True(fixture.BranchExists(branch)));
        Assert.False(Directory.Exists(removed));
        Assert.False(fixture.BranchExists(removedBranch));
        var items = ReadItems(result.Output);
        Assert.All(partials, path => Assert.Contains(items, item =>
            ItemMatches(item, path, "partially_removed", "branch_ref_retained")));
        Assert.Contains(items, item =>
            ItemMatches(item, removed, "removed", "merged_clean"));
        var summary = ReadSummary(result.Output);
        Assert.Equal(2, summary.GetProperty("partial_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removable_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removed_count").GetInt32());
    }

    [Fact]
    public void ForceReportsExactCountForTwoIndeterminateWorktreeRemovalsAndReclaimsHealthyControl()
    {
        using var fixture = new CleanLanesFixture();
        string[] partialBranches =
        [
            "harness/remove-destructive-a-partial",
            "harness/remove-destructive-b-partial",
        ];
        var partials = partialBranches.Select(branch => fixture.AddLandedLane(branch)).ToArray();
        var partialHeads = partials.Select(fixture.Head).ToArray();
        const string removedBranch = "harness/remove-destructive-z-control";
        var removed = fixture.AddLandedLane(removedBranch);
        var removedHead = fixture.Head(removed);
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
        {
            if (fileName != "git"
                || arguments.Count != 3
                || arguments[0] != "worktree"
                || arguments[1] != "remove"
                || !partials.Contains(arguments[2], StringComparer.Ordinal))
            {
                return null;
            }

            var removal = production.Run(
                fileName,
                arguments,
                workingDirectory,
                BoundedProcessRunner.HangDetectionBudget);
            Assert.Equal(0, removal.ExitCode);
            Assert.False(fixture.WorktreeRegistered(arguments[2]));
            return new ProcessOutput(
                255,
                removal.StandardOutput,
                Encoding.UTF8.GetBytes("synthetic failure after destructive removal\n"));
        });

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.False(result.Success);
        Assert.Equal("CLEAN_LANES_PARTIAL_FAILURE count=2\n", result.Error);
        Assert.All(partials, path => Assert.False(Directory.Exists(path)));
        Assert.All(partialBranches, branch => Assert.True(fixture.BranchExists(branch)));
        Assert.False(Directory.Exists(removed));
        Assert.False(fixture.BranchExists(removedBranch));
        var items = ReadItems(result.Output);
        for (var index = 0; index < partials.Length; index++)
        {
            AssertPartialItem(
                items,
                partials[index],
                partialBranches[index],
                partialHeads[index],
                "worktree_remove_failed_state_indeterminate");
        }

        AssertMergedWorktreeItem(
            items,
            removed,
            removedBranch,
            removedHead,
            "removed",
            "merged_clean");
        var summary = ReadSummary(result.Output);
        Assert.Equal("clean_lanes_summary", summary.GetProperty("event").GetString());
        Assert.Equal(3, summary.GetProperty("item_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removable_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removed_count").GetInt32());
        Assert.Equal(2, summary.GetProperty("partial_count").GetInt32());
    }

    [Fact]
    public void ForceRechecksLockAndRetainsLaneWhenItLocksAfterClassification()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/locks-before-remove");
        var probeCalls = 0;

        var result = fixture.RunWithLaneProcessProbe(
            (canonicalLanePath, _) =>
            {
                Assert.Equal(lane, canonicalLanePath);
                probeCalls++;
                if (probeCalls == 1) fixture.LockLane(lane);
                return new LaneProcessProbeOutcome(true, false);
            },
            "--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("locked", ReasonFor(result.Output, lane));
        Assert.Equal(1, probeCalls);
    }

    [Fact]
    public void ForceRechecksProcessAndRetainsLaneWhenItBecomesBusy()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/busy-before-remove");
        var probeCalls = 0;

        var result = fixture.RunWithLaneProcessProbe(
            (canonicalLanePath, _) =>
            {
                Assert.Equal(lane, canonicalLanePath);
                probeCalls++;
                return new LaneProcessProbeOutcome(true, probeCalls > 1);
            },
            "--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("in_use", ReasonFor(result.Output, lane));
        Assert.Equal(2, probeCalls);
    }

    [Fact]
    public void ForceRechecksProcessAndRetainsLaneWhenProbeBecomesUnknown()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/unknown-before-remove");
        var probeCalls = 0;

        var result = fixture.RunWithLaneProcessProbe(
            (canonicalLanePath, _) =>
            {
                Assert.Equal(lane, canonicalLanePath);
                probeCalls++;
                return new LaneProcessProbeOutcome(probeCalls == 1, false);
            },
            "--force");

        Assert.True(result.Success, result.Error);
        Assert.Equal(2, probeCalls);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("in_use_unknown", ReasonFor(result.Output, lane));
        Assert.Equal(0, ReadSummary(result.Output).GetProperty("removable_count").GetInt32());
    }

    [Fact]
    public void ForceRetainsLaneAndContinuesWhenLockRefreshFails()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/refresh-a-failure");
        var removed = fixture.AddLandedLane("harness/refresh-z-control");
        var inventoryCalls = 0;
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
        {
            if (fileName != "git"
                || !arguments.Take(2).SequenceEqual(["worktree", "list"]))
            {
                return null;
            }

            inventoryCalls++;
            return inventoryCalls == 2
                ? new ProcessOutput(
                    1,
                    [],
                    Encoding.UTF8.GetBytes("refresh failed\n"))
                : null;
        });

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.True(result.Success, result.Error);
        Assert.Equal(3, inventoryCalls);
        Assert.True(Directory.Exists(retained));
        Assert.False(Directory.Exists(removed));
        Assert.Equal("unreadable", ReasonFor(result.Output, retained));
        Assert.Equal("merged_clean", ReasonFor(result.Output, removed));
        Assert.Equal(1, ReadSummary(result.Output).GetProperty("removable_count").GetInt32());
    }

    private static bool IsLaneGit(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        string lane,
        params string[] expectedArguments) =>
        fileName == "git"
        && string.Equals(workingDirectory, lane, StringComparison.Ordinal)
        && arguments.SequenceEqual(expectedArguments);

    private static ProcessOutput GitFailure(string message) =>
        new(128, [], Encoding.UTF8.GetBytes(message + "\n"));

    private static void AssertRetainedAndControlReclaimed(
        CommandResult result,
        string retained,
        string removed,
        string retainedReason)
    {
        Assert.True(result.Success, result.Error);
        Assert.Empty(result.Error);
        Assert.True(Directory.Exists(retained));
        Assert.False(Directory.Exists(removed));
        var items = ReadItems(result.Output);
        Assert.Contains(items, item =>
            ItemMatches(item, retained, "skipped", retainedReason));
        Assert.Contains(items, item =>
            ItemMatches(item, removed, "removed", "merged_clean"));
        var summary = ReadSummary(result.Output);
        Assert.Equal(1, summary.GetProperty("removable_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("removed_count").GetInt32());
    }

    private static void AssertPartialItem(
        IReadOnlyList<JsonElement> items,
        string path,
        string branch,
        string head,
        string reason) =>
        AssertMergedWorktreeItem(items, path, branch, head, "partially_removed", reason);

    private static void AssertMergedWorktreeItem(
        IReadOnlyList<JsonElement> items,
        string path,
        string branch,
        string head,
        string action,
        string reason)
    {
        var item = items.Single(candidate =>
            candidate.GetProperty("path").GetString() == path);
        Assert.Equal("merged_worktree", item.GetProperty("kind").GetString());
        Assert.Equal(path, item.GetProperty("path").GetString());
        Assert.Equal(branch, item.GetProperty("branch").GetString());
        Assert.Equal(head, item.GetProperty("head").GetString());
        Assert.Equal(action, item.GetProperty("action").GetString());
        Assert.Equal(reason, item.GetProperty("reason").GetString());
    }

    private static ProcessOutput SuccessfulPrOutput(string branch, string head) =>
        new(
            0,
            JsonSerializer.SerializeToUtf8Bytes(new[]
            {
                new
                {
                    state = "MERGED",
                    headRefName = branch,
                    headRefOid = head,
                    mergeCommit = new { oid = head },
                },
            }),
            []);

    private static ProcessOutput IdleLsofOutput() =>
        LsofOutput(Path.Combine(Path.GetTempPath(), "clean-lanes-outside-probe"));

    private static ProcessOutput LsofOutput(string path) =>
        new(
            0,
            Encoding.UTF8.GetBytes($"p123\0fcwd\0n{path}\0"),
            []);
}
