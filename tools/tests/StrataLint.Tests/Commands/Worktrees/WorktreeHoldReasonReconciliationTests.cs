using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void SuccessfulHoldAcceptsGitNormalizedTrailingWhitespaceReason()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/hold-reason-trailing-whitespace");
        var now = new DateTimeOffset(2031, 2, 3, 4, 5, 6, 789, TimeSpan.Zero);

        var result = WorktreeHoldCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", lane, "--reason", "legitimate holder "],
            fixture.CreateRunner(),
            now);

        Assert.True(result.Success, result.Error);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("held", receipt.GetProperty("action").GetString());
        var effectiveReason = receipt.GetProperty("effective_reason").GetString()!;
        Assert.Matches(
            "^held_at_utc=2031-02-03T04:05:06\\.789Z; invocation_id=[0-9a-f]{32}; "
                + "reason=legitimate holder$",
            effectiveReason);
        Assert.Contains(
            $"locked {effectiveReason}",
            fixture.WorktreeBlock(lane),
            StringComparison.Ordinal);
    }

    [Fact]
    public void HoldReasonsUseDistinctInvocationIdentitiesAtTheSameTimestamp()
    {
        using var fixture = new CleanLanesFixture();
        var firstLane = fixture.AddLandedLane("harness/hold-reason-identity-first");
        var secondLane = fixture.AddLandedLane("harness/hold-reason-identity-second");
        var now = new DateTimeOffset(2031, 2, 3, 4, 5, 6, 789, TimeSpan.Zero);

        var first = WorktreeHoldCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", firstLane, "--reason", "same holder"],
            fixture.CreateRunner(),
            now);
        var second = WorktreeHoldCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", secondLane, "--reason", "same holder"],
            fixture.CreateRunner(),
            now);

        Assert.True(first.Success, first.Error);
        Assert.True(second.Success, second.Error);
        var firstReason = ReadHoldReceipt(first).GetProperty("effective_reason").GetString()!;
        var secondReason = ReadHoldReceipt(second).GetProperty("effective_reason").GetString()!;
        Assert.NotEqual(firstReason, secondReason);
        Assert.Matches("; invocation_id=[0-9a-f]{32}; reason=same holder$", firstReason);
        Assert.Matches("; invocation_id=[0-9a-f]{32}; reason=same holder$", secondReason);
    }

    [Fact]
    public void SuccessfulHoldRefusesSameHumanReadableReasonAbaReplacement()
    {
        using var fixture = new CleanLanesFixture();
        var branch = "harness/hold-reason-same-human-aba";
        var lane = fixture.AddLandedLane(branch);
        var replacementLane = fixture.AddLandedLane("harness/hold-reason-same-human-source");
        var now = new DateTimeOffset(2031, 2, 3, 4, 5, 6, 789, TimeSpan.Zero);
        var replacement = WorktreeHoldCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", replacementLane, "--reason", "same holder"],
            fixture.CreateRunner(),
            now);
        Assert.True(replacement.Success, replacement.Error);
        var observedReason = ReadHoldReceipt(replacement)
            .GetProperty("effective_reason")
            .GetString()!;
        string? expectedReason = null;
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
        {
            if (!IsGitMutation(fileName, arguments, "lock")) return null;
            expectedReason = arguments[3];
            fixture.RestoreLane(lane, branch, locked: false);
            fixture.LockLane(lane, observedReason);
            return new ProcessOutput(0, [], []);
        });

        var result = WorktreeHoldCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", lane, "--reason", "same holder"],
            runner,
            now);

        Assert.False(result.Success);
        Assert.NotNull(expectedReason);
        Assert.NotEqual(expectedReason, observedReason);
        Assert.Contains("reason=same holder", expectedReason, StringComparison.Ordinal);
        Assert.Contains("reason=same holder", observedReason, StringComparison.Ordinal);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("worktree_mutation_state_indeterminate", receipt.GetProperty("error").GetString());
        Assert.Equal(expectedReason, receipt.GetProperty("expected_reason").GetString());
        Assert.Equal(observedReason, receipt.GetProperty("observed_reason").GetString());
    }

    [Theory]
    [InlineData("caller holder", "other holder")]
    [InlineData("other holder", "caller holder")]
    public void SuccessfulHoldRefusesSameIdentitySameBitDifferentObservedReason(
        string requestedReason,
        string otherReason)
    {
        using var fixture = new CleanLanesFixture();
        var branch = "harness/hold-reason-aba";
        var lane = fixture.AddLandedLane(branch);
        var now = new DateTimeOffset(2031, 2, 3, 4, 5, 6, 789, TimeSpan.Zero);
        string? expectedReason = null;
        string? observedReason = null;
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
        {
            if (!IsGitMutation(fileName, arguments, "lock")) return null;
            expectedReason = arguments[3];
            observedReason = expectedReason[..^requestedReason.Length] + otherReason;
            fixture.RestoreLane(lane, branch, locked: false);
            fixture.LockLane(lane, observedReason);
            return new ProcessOutput(0, [], []);
        });

        var result = WorktreeHoldCommand.Run(
            fixture.RepositoryWorkingDirectory,
            ["hold", "--path", lane, "--reason", requestedReason],
            runner,
            now);

        Assert.False(result.Success);
        Assert.NotNull(expectedReason);
        Assert.NotNull(observedReason);
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("worktree_mutation_state_indeterminate", receipt.GetProperty("error").GetString());
        Assert.Equal(expectedReason, receipt.GetProperty("expected_reason").GetString());
        Assert.Equal(observedReason, receipt.GetProperty("observed_reason").GetString());
        Assert.Equal(expectedReason, receipt.GetProperty("effective_reason").GetString());
    }

}
