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

        var first = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", lane, "--reason", "original holder"]);
        var second = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", lane, "--reason", "replacement holder"]);

        Assert.True(first.Success, first.Error);
        Assert.True(second.Success, second.Error);
        var originalReason = ReadHoldReceipt(first).GetProperty("effective_reason").GetString();
        var repeated = ReadHoldReceipt(second);
        Assert.Equal("already_held", repeated.GetProperty("action").GetString());
        Assert.Equal(originalReason, repeated.GetProperty("effective_reason").GetString());
        Assert.Contains("reason=original holder", originalReason, StringComparison.Ordinal);
        Assert.DoesNotContain("replacement holder", fixture.WorktreeBlock(lane), StringComparison.Ordinal);
    }

    [Fact]
    public void ReleaseOnUnlockedLaneIsIdempotent()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/release-unlocked");
        var before = fixture.WorktreeInventory();

        var result = WorktreeCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["release", "--path", lane]);

        Assert.True(result.Success, result.Error);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("release", receipt.GetProperty("operation").GetString());
        Assert.Equal("already_released", receipt.GetProperty("action").GetString());
        Assert.Equal(JsonValueKind.Null, receipt.GetProperty("effective_reason").ValueKind);
        Assert.Equal(before, fixture.WorktreeInventory());
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
        Assert.Equal(expectedError, ReadHoldReceipt(result).GetProperty("error").GetString());
        Assert.Equal(before, fixture.WorktreeInventory());
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

        internal string WorktreeBlock(string path) =>
            WorktreeInventory()
                .Split("\n\n", StringSplitOptions.RemoveEmptyEntries)
                .Single(block => block.StartsWith($"worktree {path}\n", StringComparison.Ordinal));
    }
}
