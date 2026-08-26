using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void ThrowingPullRequestProbeRetainsLaneAndContinuesSweep()
    {
        using var fixture = new CleanLanesFixture();
        const string retainedBranch = "harness/throwing-pr-a-retained";
        const string removedBranch = "harness/throwing-pr-z-control";
        var retained = fixture.AddLandedLane(retainedBranch);
        var removed = fixture.AddLandedLane(removedBranch);
        var removedHead = fixture.Head(removed);

        var result = fixture.RunWithProbes(
            (_, branch, _) => branch == retainedBranch
                ? throw new InvalidOperationException("synthetic PR probe failure")
                : new PullRequestProbeOutcome(
                    true,
                    [new PullRequestInfo(branch, removedHead, "MERGED", removedHead)]),
            static (_, _) => new LaneProcessProbeOutcome(true, false),
            "--force",
            "--lanes-only");

        AssertRetainedAndControlReclaimed(result, retained, removed, "pr_unknown");
    }

    [Fact]
    public void ThrowingInitialProcessProbeRetainsLaneAndContinuesSweep()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/throwing-process-a-retained");
        var removed = fixture.AddLandedLane("harness/throwing-process-z-control");

        var result = fixture.RunWithLaneProcessProbe(
            (path, _) => string.Equals(path, retained, StringComparison.Ordinal)
                ? throw new InvalidOperationException("synthetic initial process probe failure")
                : new LaneProcessProbeOutcome(true, false),
            "--force",
            "--lanes-only");

        AssertRetainedAndControlReclaimed(result, retained, removed, "in_use_unknown");
    }

    [Fact]
    public void ThrowingRemovalProcessProbeRetainsLaneAndContinuesSweep()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/throwing-recheck-a-retained");
        var removed = fixture.AddLandedLane("harness/throwing-recheck-z-control");
        var probeCalls = new Dictionary<string, int>(StringComparer.Ordinal);

        var result = fixture.RunWithLaneProcessProbe(
            (path, _) =>
            {
                probeCalls[path] = probeCalls.GetValueOrDefault(path) + 1;
                if (string.Equals(path, retained, StringComparison.Ordinal)
                    && probeCalls[path] == 2)
                {
                    throw new InvalidOperationException("synthetic removal process probe failure");
                }

                return new LaneProcessProbeOutcome(true, false);
            },
            "--force",
            "--lanes-only");

        Assert.Equal(2, probeCalls[retained]);
        Assert.Equal(2, probeCalls[removed]);
        AssertRetainedAndControlReclaimed(result, retained, removed, "in_use_unknown");
    }

    [Fact]
    public void ForceRetainsLaneAndContinuesWhenRefreshedInventoryOmitsIt()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/refresh-omitted-a-retained");
        var removed = fixture.AddLandedLane("harness/refresh-omitted-z-control");
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
            var recordStart = inventory.IndexOf(
                $"worktree {retained}\0",
                StringComparison.Ordinal);
            var nextRecord = inventory.IndexOf(
                "worktree ",
                recordStart + 1,
                StringComparison.Ordinal);
            Assert.True(recordStart >= 0);
            var withoutRetained = inventory.Remove(
                recordStart,
                (nextRecord < 0 ? inventory.Length : nextRecord) - recordStart);

            return new ProcessOutput(
                output.ExitCode,
                Encoding.UTF8.GetBytes(withoutRetained),
                output.StandardError);
        });

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.Equal(3, inventoryCalls);
        AssertRetainedAndControlReclaimed(result, retained, removed, "unreadable");
    }
}
