using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
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
        var expectedReason = $"held_at_utc=2031-02-03T04:05:06.789Z; reason={requestedReason}";
        var observedReason = $"held_at_utc=2031-02-03T04:05:06.789Z; reason={otherReason}";
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
        {
            if (!IsGitMutation(fileName, arguments, "lock")) return null;
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
        var receipt = ReadHoldReceipt(result);
        Assert.Equal("worktree_mutation_state_indeterminate", receipt.GetProperty("error").GetString());
        Assert.Equal(expectedReason, receipt.GetProperty("expected_reason").GetString());
        Assert.Equal(observedReason, receipt.GetProperty("observed_reason").GetString());
        Assert.Equal(expectedReason, receipt.GetProperty("effective_reason").GetString());
    }
}
