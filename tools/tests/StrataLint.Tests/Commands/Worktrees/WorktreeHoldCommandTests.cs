using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void HoldLocksManagedLaneAndPorcelainReportsTheEffectiveReason()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/hold-porcelain");

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", lane, "--reason", "fixture session"]);

        Assert.True(result.Success, result.Error);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("hold", receipt.GetProperty("operation").GetString());
        Assert.Equal("held", receipt.GetProperty("action").GetString());
        Assert.Equal(lane, receipt.GetProperty("path").GetString());
        Assert.Equal("harness/hold-porcelain", receipt.GetProperty("branch").GetString());
        var effectiveReason = receipt.GetProperty("effective_reason").GetString()!;
        Assert.Matches(
            "^held_at_utc=[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}\\.[0-9]{3}Z; reason=fixture session$",
            effectiveReason);
        Assert.Contains(
            $"locked {effectiveReason}",
            fixture.WorktreeBlock(lane),
            StringComparison.Ordinal);
    }

    [Fact]
    public void HoldTwiceIsIdempotentAndPreservesTheOriginalReason()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/hold-twice");
        var runner = fixture.CreateRunner();

        var first = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", lane, "--reason", "original holder"],
            runner);
        var second = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", lane, "--reason", "replacement holder"],
            runner);

        Assert.True(first.Success, first.Error);
        Assert.True(second.Success, second.Error);
        var originalReason = ReadHoldReceipt(first).GetProperty("effective_reason").GetString();
        var repeated = ReadHoldReceipt(second);
        Assert.Equal("already_held", repeated.GetProperty("action").GetString());
        Assert.Equal(originalReason, repeated.GetProperty("effective_reason").GetString());
        Assert.Contains("reason=original holder", originalReason, StringComparison.Ordinal);
        Assert.DoesNotContain("replacement holder", fixture.WorktreeBlock(lane), StringComparison.Ordinal);
        Assert.Single(runner.Invocations, invocation =>
            IsGitMutation(invocation, "lock"));
    }

    [Fact]
    public void ReleaseOnUnlockedLaneIsIdempotent()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/release-unlocked");
        var before = fixture.WorktreeInventory();
        var runner = fixture.CreateRunner();

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["release", "--path", lane],
            runner);

        Assert.True(result.Success, result.Error);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("release", receipt.GetProperty("operation").GetString());
        Assert.Equal("already_released", receipt.GetProperty("action").GetString());
        Assert.Equal(JsonValueKind.Null, receipt.GetProperty("effective_reason").ValueKind);
        Assert.Equal(before, fixture.WorktreeInventory());
        Assert.DoesNotContain(runner.Invocations, invocation =>
            IsGitMutation(invocation, "unlock"));
    }

    [Theory]
    [InlineData("hold")]
    [InlineData("release")]
    public void UnregisteredPathIsRefusedWithoutMutation(string operation)
    {
        using var fixture = new CleanLanesFixture();
        using var outside = new TemporaryDirectory();
        var unknown = Path.Combine(outside.Path, "not-registered");
        var before = fixture.WorktreeInventory();

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            [operation, "--path", unknown]);

        Assert.False(result.Success);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("refused", receipt.GetProperty("action").GetString());
        Assert.Equal("unregistered_worktree", receipt.GetProperty("error").GetString());
        Assert.Equal(JsonValueKind.Null, receipt.GetProperty("branch").ValueKind);
        Assert.False(Directory.Exists(unknown));
        Assert.Equal(before, fixture.WorktreeInventory());
    }

    [Theory]
    [InlineData("hold")]
    [InlineData("release")]
    public void NonManagedBranchIsRefusedWithoutMutation(string operation)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddNonManagedLane("scratch/not-managed");
        var before = fixture.WorktreeInventory();

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            [operation, "--path", lane]);

        Assert.False(result.Success);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("refused", receipt.GetProperty("action").GetString());
        Assert.Equal("not_managed_lane", receipt.GetProperty("error").GetString());
        Assert.Equal("scratch/not-managed", receipt.GetProperty("branch").GetString());
        Assert.Equal(before, fixture.WorktreeInventory());
        Assert.DoesNotContain("locked", fixture.WorktreeBlock(lane), StringComparison.Ordinal);
    }

    [Fact]
    public void HoldWithoutPathReturnsOneStructuredInvalidArgumentsLine()
    {
        using var fixture = new CleanLanesFixture();

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold"]);

        Assert.False(result.Success);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("refused", receipt.GetProperty("action").GetString());
        Assert.Equal("invalid_arguments", receipt.GetProperty("error").GetString());
        Assert.Equal(JsonValueKind.Null, receipt.GetProperty("path").ValueKind);
    }

    [Fact]
    public void InventoryFailureIsNamedAndDoesNotMutateTheLane()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/hold-inventory-failure");
        var before = fixture.WorktreeInventory();
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
            fileName == "git"
                && arguments.SequenceEqual(["worktree", "list", "--porcelain", "-z"])
                    ? FailedGit("injected inventory failure")
                    : null);

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", lane],
            runner);

        Assert.False(result.Success);
        Assert.Equal(
            "inventory_failed",
            ReadHoldReceipt(result).GetProperty("error").GetString());
        Assert.Equal(before, fixture.WorktreeInventory());
    }

    [Fact]
    public void MalformedInventoryIsNamedAndDoesNotMutateTheLane()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/hold-malformed-inventory");
        var before = fixture.WorktreeInventory();
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
            fileName == "git"
                && arguments.SequenceEqual(["worktree", "list", "--porcelain", "-z"])
                    ? new ProcessOutput(
                        0,
                        System.Text.Encoding.UTF8.GetBytes(
                            $"worktree {lane}\0worktree {lane}\0\0"),
                        [])
                    : null);

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", lane],
            runner);

        Assert.False(result.Success);
        Assert.Equal(
            "inventory_malformed",
            ReadHoldReceipt(result).GetProperty("error").GetString());
        Assert.Equal(before, fixture.WorktreeInventory());
    }

    [Theory]
    [InlineData("hold", "lock", "lock_failed")]
    [InlineData("release", "unlock", "unlock_failed")]
    public void GitMutationFailureIsNamedAndPreservesTheOriginalLockState(
        string operation,
        string gitMutation,
        string expectedError)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane($"harness/{operation}-mutation-failure");
        if (operation == "release") fixture.LockLane(lane);
        var before = fixture.WorktreeInventory();
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
            fileName == "git"
                && arguments.Count >= 2
                && arguments[0] == "worktree"
                && arguments[1] == gitMutation
                    ? FailedGit($"injected {gitMutation} failure")
                    : null);

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            [operation, "--path", lane],
            runner);

        Assert.False(result.Success);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal(expectedError, receipt.GetProperty("error").GetString());
        Assert.Equal(
            operation == "release" ? "fixture session" : null,
            receipt.GetProperty("effective_reason").GetString());
        Assert.Equal(2, runner.Invocations.Count(IsWorktreeInventory));
        Assert.Equal(before, fixture.WorktreeInventory());
    }

    [Theory]
    [InlineData("hold", "lock", "already_held")]
    [InlineData("release", "unlock", "already_released")]
    public void GitMutationFailureRereadsInventoryAndAcceptsConcurrentlyAchievedState(
        string operation,
        string gitMutation,
        string expectedAction)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane($"harness/{operation}-concurrent-idempotence");
        if (operation == "release") fixture.LockLane(lane);
        var mutationObserved = false;
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
        {
            if (mutationObserved
                || fileName != "git"
                || arguments.Count < 2
                || arguments[0] != "worktree"
                || arguments[1] != gitMutation)
            {
                return null;
            }

            mutationObserved = true;
            if (operation == "hold")
            {
                fixture.LockLane(lane);
            }
            else
            {
                fixture.UnlockLane(lane);
            }

            return FailedGit($"concurrent invocation already completed {gitMutation}");
        });

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            [operation, "--path", lane],
            runner);

        Assert.True(result.Success, result.Error);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal(expectedAction, receipt.GetProperty("action").GetString());
        Assert.Equal(
            operation == "hold" ? "fixture session" : null,
            receipt.GetProperty("effective_reason").GetString());
        Assert.Equal(2, runner.Invocations.Count(IsWorktreeInventory));
    }

    [Theory]
    [InlineData("hold", "lock")]
    [InlineData("release", "unlock")]
    public void SuccessfulGitMutationRefusesIndeterminateReceiptWhenPathNowNamesDifferentBranch(
        string operation,
        string gitMutation)
    {
        using var fixture = new CleanLanesFixture();
        var originalBranch = $"harness/{operation}-success-original";
        var replacementBranch = $"harness/{operation}-success-replacement";
        var lane = fixture.AddLandedLane(originalBranch);
        if (operation == "release") fixture.LockLane(lane);
        var mutationObserved = false;
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
        {
            if (mutationObserved || !IsGitMutation(fileName, arguments, gitMutation))
            {
                return null;
            }

            mutationObserved = true;
            fixture.ReplaceLane(lane, replacementBranch, operation == "release");
            return null;
        });

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            [operation, "--path", lane],
            runner);

        Assert.False(result.Success);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("worktree_mutation_state_indeterminate", receipt.GetProperty("error").GetString());
        Assert.Equal(originalBranch, receipt.GetProperty("branch").GetString());
        Assert.Equal(originalBranch, receipt.GetProperty("expected_branch").GetString());
        Assert.Equal(replacementBranch, receipt.GetProperty("observed_branch").GetString());
        Assert.Contains(
            "mutation may have applied to a different lane",
            receipt.GetProperty("detail").GetString(),
            StringComparison.Ordinal);
        Assert.Contains(
            "no undo was attempted",
            receipt.GetProperty("detail").GetString(),
            StringComparison.Ordinal);
        Assert.Equal(2, runner.Invocations.Count(IsWorktreeInventory));
        Assert.Single(runner.Invocations, invocation => IsGitMutation(invocation, gitMutation));
        Assert.Contains(
            $"branch refs/heads/{replacementBranch}",
            fixture.WorktreeBlock(lane),
            StringComparison.Ordinal);
        Assert.Equal(
            operation == "hold",
            fixture.WorktreeBlock(lane).Contains("locked", StringComparison.Ordinal));
    }

    [Fact]
    public void SuccessfulHoldRefusesWhenObservedSameLaneIdentityIsUnlocked()
    {
        AssertSuccessfulMutationRefusesObservedOppositeLockState(
            "hold",
            "lock",
            observedLocked: false);
    }

    [Fact]
    public void SuccessfulReleaseRefusesWhenObservedSameLaneIdentityIsLocked()
    {
        AssertSuccessfulMutationRefusesObservedOppositeLockState(
            "release",
            "unlock",
            observedLocked: true);
    }

    [Theory]
    [InlineData("hold", "lock")]
    [InlineData("release", "unlock")]
    public void FailedGitMutationDoesNotReconcileAgainstReplacementBranch(
        string operation,
        string gitMutation)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane($"harness/{operation}-failure-original");
        if (operation == "release") fixture.LockLane(lane);
        var mutationObserved = false;
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
        {
            if (mutationObserved || !IsGitMutation(fileName, arguments, gitMutation))
            {
                return null;
            }

            mutationObserved = true;
            fixture.ReplaceLane(
                lane,
                $"harness/{operation}-failure-replacement",
                operation == "hold");
            return FailedGit($"injected {gitMutation} failure after replacement");
        });

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            [operation, "--path", lane],
            runner);

        Assert.False(result.Success);
        Assert.Equal(
            operation == "hold" ? "lock_failed" : "unlock_failed",
            ReadHoldReceipt(result).GetProperty("error").GetString());
        Assert.Equal(2, runner.Invocations.Count(IsWorktreeInventory));
        Assert.Single(runner.Invocations, invocation => IsGitMutation(invocation, gitMutation));
    }

    [Theory]
    [InlineData("hold", "lock")]
    [InlineData("release", "unlock")]
    public void SuccessfulGitMutationReportsIndeterminateWhenInventoryRefreshFails(
        string operation,
        string gitMutation)
    {
        AssertSuccessfulMutationRefreshIsIndeterminate(
            operation,
            gitMutation,
            static (_, _) => FailedGit("injected successful-mutation refresh failure"));
    }

    [Fact]
    public void SuccessfulHoldReportsIndeterminateWhenInventoryRefreshThrows()
    {
        AssertSuccessfulMutationRefreshIsIndeterminate(
            "hold",
            "lock",
            static (_, _) => throw new IOException("injected hold refresh exception"));
    }

    [Fact]
    public void SuccessfulReleaseReportsIndeterminateWhenInventoryRefreshThrows()
    {
        AssertSuccessfulMutationRefreshIsIndeterminate(
            "release",
            "unlock",
            static (_, _) => throw new IOException("injected release refresh exception"));
    }

    [Theory]
    [InlineData("hold", "lock")]
    [InlineData("release", "unlock")]
    public void SuccessfulGitMutationReportsIndeterminateWhenRefreshedInventoryIsMalformed(
        string operation,
        string gitMutation)
    {
        AssertSuccessfulMutationRefreshIsIndeterminate(
            operation,
            gitMutation,
            static (_, lane) => new ProcessOutput(
                0,
                System.Text.Encoding.UTF8.GetBytes(
                    $"worktree {lane}\0worktree {lane}\0\0"),
                []));
    }

    [Theory]
    [InlineData("hold", "lock")]
    [InlineData("release", "unlock")]
    public void SuccessfulGitMutationReportsIndeterminateWhenLaneIsMissingFromRefreshedInventory(
        string operation,
        string gitMutation)
    {
        AssertSuccessfulMutationRefreshIsIndeterminate(
            operation,
            gitMutation,
            static (fixture, _) => new ProcessOutput(
                0,
                System.Text.Encoding.UTF8.GetBytes(
                    $"worktree {fixture.RepositoryWorkingDirectory}\0"
                    + "branch refs/heads/dev\0\0"),
                []));
    }

    [Theory]
    [InlineData("hold", "lock")]
    [InlineData("release", "unlock")]
    public void FailedGitMutationFailsClosedWhenInventoryRefreshFails(
        string operation,
        string gitMutation)
    {
        AssertFailedMutationRefreshIsNotReconciled(
            operation,
            gitMutation,
            static (_, _) => FailedGit("injected refresh failure"));
    }

    [Theory]
    [InlineData("hold", "lock")]
    [InlineData("release", "unlock")]
    public void FailedGitMutationFailsClosedWhenRefreshedInventoryIsMalformed(
        string operation,
        string gitMutation)
    {
        AssertFailedMutationRefreshIsNotReconciled(
            operation,
            gitMutation,
            static (fixture, lane) => new ProcessOutput(
                0,
                System.Text.Encoding.UTF8.GetBytes(
                    $"worktree {lane}\0worktree {lane}\0\0"),
                []));
    }

    [Theory]
    [InlineData("hold", "lock")]
    [InlineData("release", "unlock")]
    public void FailedGitMutationFailsClosedWhenLaneIsMissingFromRefreshedInventory(
        string operation,
        string gitMutation)
    {
        AssertFailedMutationRefreshIsNotReconciled(
            operation,
            gitMutation,
            static (fixture, _) => new ProcessOutput(
                0,
                System.Text.Encoding.UTF8.GetBytes(
                    $"worktree {fixture.RepositoryWorkingDirectory}\0"
                    + "branch refs/heads/dev\0\0"),
                []));
    }

    [Fact]
    public void HeldReclaimableLaneIsSkippedLockedThenReleasedLaneIsReclaimed()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/hold-clean-lanes-bridge");

        var beforeHold = fixture.Run();
        Assert.True(beforeHold.Success, beforeHold.Error);
        Assert.Equal("merged_clean", ReasonFor(beforeHold.Output, lane));
        AssertItemProperty(ReadItems(beforeHold.Output), "path", lane, "action", "would_remove");

        var hold = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", lane, "--reason", "active clean-lanes session"]);
        Assert.True(hold.Success, hold.Error);

        var whileHeldDryRun = fixture.Run();
        Assert.True(whileHeldDryRun.Success, whileHeldDryRun.Error);
        Assert.True(Directory.Exists(lane));
        Assert.True(fixture.WorktreeRegistered(lane));
        Assert.Equal("locked", ReasonFor(whileHeldDryRun.Output, lane));
        AssertItemProperty(
            ReadItems(whileHeldDryRun.Output),
            "path",
            lane,
            "action",
            "skipped");

        var whileHeld = fixture.Run("--force");
        Assert.True(whileHeld.Success, whileHeld.Error);
        Assert.True(Directory.Exists(lane));
        Assert.True(fixture.WorktreeRegistered(lane));
        Assert.Equal("locked", ReasonFor(whileHeld.Output, lane));
        AssertItemProperty(ReadItems(whileHeld.Output), "path", lane, "action", "skipped");

        var release = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["release", "--path", lane]);
        Assert.True(release.Success, release.Error);
        Assert.Equal("released", ReadHoldReceipt(release).GetProperty("action").GetString());

        var afterRelease = fixture.Run("--force");
        Assert.True(afterRelease.Success, afterRelease.Error);
        Assert.False(Directory.Exists(lane));
        Assert.False(fixture.WorktreeRegistered(lane));
        Assert.Equal("merged_clean", ReasonFor(afterRelease.Output, lane));
        AssertItemProperty(ReadItems(afterRelease.Output), "path", lane, "action", "removed");
    }

    private static JsonElement ReadHoldReceipt(CommandResult result)
    {
        var payload = result.Success ? result.Output : result.Error;
        Assert.EndsWith("\n", payload, StringComparison.Ordinal);
        var line = Assert.Single(payload.Split('\n', StringSplitOptions.RemoveEmptyEntries));
        using var document = JsonDocument.Parse(line);
        Assert.Equal("worktree_hold_state", document.RootElement.GetProperty("event").GetString());
        return document.RootElement.Clone();
    }

    private static ProcessOutput FailedGit(string message) =>
        new(128, [], System.Text.Encoding.UTF8.GetBytes(message + "\n"));

    private static void AssertFailedMutationRefreshIsNotReconciled(
        string operation,
        string gitMutation,
        Func<CleanLanesFixture, string, ProcessOutput> refreshedInventory)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane($"harness/{operation}-refresh-fail-closed");
        if (operation == "release") fixture.LockLane(lane);
        var mutationObserved = false;
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
        {
            if (IsGitMutation(fileName, arguments, gitMutation))
            {
                mutationObserved = true;
                return FailedGit($"injected {gitMutation} failure");
            }

            return mutationObserved && IsWorktreeInventory(fileName, arguments)
                ? refreshedInventory(fixture, lane)
                : null;
        });

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            [operation, "--path", lane],
            runner);

        Assert.False(result.Success);
        Assert.Equal(
            operation == "hold" ? "lock_failed" : "unlock_failed",
            ReadHoldReceipt(result).GetProperty("error").GetString());
        Assert.Equal(2, runner.Invocations.Count(IsWorktreeInventory));
        Assert.Single(runner.Invocations, invocation => IsGitMutation(invocation, gitMutation));
    }

    private static void AssertSuccessfulMutationRefreshIsIndeterminate(
        string operation,
        string gitMutation,
        Func<CleanLanesFixture, string, ProcessOutput> refreshedInventory)
    {
        using var fixture = new CleanLanesFixture();
        var branch = $"harness/{operation}-success-refresh-fail-closed";
        var lane = fixture.AddLandedLane(branch);
        if (operation == "release") fixture.LockLane(lane);
        var mutationObserved = false;
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
        {
            if (IsGitMutation(fileName, arguments, gitMutation))
            {
                mutationObserved = true;
                return null;
            }

            return mutationObserved && IsWorktreeInventory(fileName, arguments)
                ? refreshedInventory(fixture, lane)
                : null;
        });

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            [operation, "--path", lane],
            runner);

        Assert.False(result.Success);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("worktree_mutation_state_indeterminate", receipt.GetProperty("error").GetString());
        Assert.Equal(branch, receipt.GetProperty("expected_branch").GetString());
        Assert.Equal(JsonValueKind.Null, receipt.GetProperty("observed_branch").ValueKind);
        Assert.Contains(
            "no undo was attempted",
            receipt.GetProperty("detail").GetString(),
            StringComparison.Ordinal);
        Assert.Equal(2, runner.Invocations.Count(IsWorktreeInventory));
        Assert.Single(runner.Invocations, invocation => IsGitMutation(invocation, gitMutation));
        Assert.Equal(
            operation == "hold",
            fixture.WorktreeBlock(lane).Contains("locked", StringComparison.Ordinal));
    }

    private static void AssertSuccessfulMutationRefusesObservedOppositeLockState(
        string operation,
        string gitMutation,
        bool observedLocked)
    {
        using var fixture = new CleanLanesFixture();
        var originalBranch = $"harness/{operation}-same-identity-original";
        var replacementBranch = $"harness/{operation}-same-identity-replacement";
        var lane = fixture.AddLandedLane(originalBranch);
        if (operation == "release") fixture.LockLane(lane);
        var mutationObserved = false;
        var originalOccupantRestored = false;
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
        {
            if (!mutationObserved && IsGitMutation(fileName, arguments, gitMutation))
            {
                mutationObserved = true;
                fixture.ReplaceLane(lane, replacementBranch, locked: operation == "release");
                return null;
            }

            if (mutationObserved
                && !originalOccupantRestored
                && IsWorktreeInventory(fileName, arguments))
            {
                originalOccupantRestored = true;
                fixture.RestoreLane(lane, originalBranch, observedLocked);
            }

            return null;
        });

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            [operation, "--path", lane],
            runner);

        Assert.False(result.Success);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("worktree_mutation_state_indeterminate", receipt.GetProperty("error").GetString());
        Assert.Equal(originalBranch, receipt.GetProperty("branch").GetString());
        Assert.Equal(originalBranch, receipt.GetProperty("expected_branch").GetString());
        Assert.Equal(originalBranch, receipt.GetProperty("observed_branch").GetString());
        Assert.Equal(operation == "hold", receipt.GetProperty("expected_locked").GetBoolean());
        Assert.Equal(observedLocked, receipt.GetProperty("observed_locked").GetBoolean());
        Assert.Contains(
            "did not verify the expected lane identity and lock state",
            receipt.GetProperty("detail").GetString(),
            StringComparison.Ordinal);
        Assert.Contains(
            "no undo was attempted",
            receipt.GetProperty("detail").GetString(),
            StringComparison.Ordinal);
        Assert.Equal(2, runner.Invocations.Count(IsWorktreeInventory));
        Assert.Single(runner.Invocations, invocation => IsGitMutation(invocation, gitMutation));
        Assert.Equal(
            observedLocked,
            fixture.WorktreeBlock(lane).Contains("locked", StringComparison.Ordinal));
    }

    private static bool IsWorktreeInventory(WorktreeProcessInvocation invocation) =>
        IsWorktreeInventory(invocation.FileName, invocation.Arguments);

    private static bool IsWorktreeInventory(
        string fileName,
        IReadOnlyList<string> arguments) =>
        fileName == "git"
        && arguments.SequenceEqual(["worktree", "list", "--porcelain", "-z"]);

    private static bool IsGitMutation(
        WorktreeProcessInvocation invocation,
        string mutation) =>
        IsGitMutation(invocation.FileName, invocation.Arguments, mutation);

    private static bool IsGitMutation(
        string fileName,
        IReadOnlyList<string> arguments,
        string mutation) =>
        fileName == "git"
        && arguments.Count >= 2
        && arguments[0] == "worktree"
        && arguments[1] == mutation;

    private sealed partial class CleanLanesFixture
    {
        internal string AddNonManagedLane(string branch)
        {
            var path = WorktreePath(branch);
            AddWorktree(branch, path);
            return Git(path, "rev-parse", "--show-toplevel").Trim();
        }

        internal string WorktreeInventory() =>
            Git(repository.Path, "worktree", "list", "--porcelain");

        internal void UnlockLane(string path) =>
            Git(repository.Path, "worktree", "unlock", path);

        internal void ReplaceLane(string path, string replacementBranch, bool locked)
        {
            var block = WorktreeBlock(path);
            if (block.Contains("locked", StringComparison.Ordinal)) UnlockLane(path);
            Git(repository.Path, "worktree", "remove", "--force", path);
            AddWorktree(replacementBranch, path);
            if (locked) LockLane(path);
        }

        internal void RestoreLane(string path, string originalBranch, bool locked)
        {
            var block = WorktreeBlock(path);
            if (block.Contains("locked", StringComparison.Ordinal)) UnlockLane(path);
            Git(repository.Path, "worktree", "remove", "--force", path);
            Git(repository.Path, "worktree", "add", path, originalBranch);
            if (locked) LockLane(path);
        }

        internal string WorktreeBlock(string path) =>
            WorktreeInventory()
                .Split("\n\n", StringSplitOptions.RemoveEmptyEntries)
                .Single(block => block.StartsWith($"worktree {path}\n", StringComparison.Ordinal));
    }
}
