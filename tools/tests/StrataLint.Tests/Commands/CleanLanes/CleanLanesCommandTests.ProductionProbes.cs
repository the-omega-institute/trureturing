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
        Assert.Contains(runner.Invocations, invocation => invocation.FileName == "gh");
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
        Assert.Contains(runner.Invocations, invocation => invocation.FileName == "lsof");
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

        var result = fixture.RunWithProductionProbes(runner);

        Assert.True(result.Success, result.Error);
        Assert.Equal("merged_clean", ReasonFor(result.Output, lane));
        Assert.Contains(runner.Invocations, invocation => invocation.FileName == "gh");
        Assert.Contains(runner.Invocations, invocation => invocation.FileName == "lsof");
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
        Assert.Contains("\"removable_count\":0", result.Output, StringComparison.Ordinal);
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
        Assert.Contains("\"removable_count\":1", result.Output, StringComparison.Ordinal);
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
