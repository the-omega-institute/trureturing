using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData("empty")]
    [InlineData("malformed")]
    [InlineData("zero")]
    [InlineData("nonzero")]
    public void UnavailableProductionBirthtimeProbeRetainsLane(string outcome)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane($"harness/birthtime-{outcome}");
        var runner = fixture.CreateRunner((fileName, _, _) =>
        {
            if (fileName != "stat") return null;
            return outcome switch
            {
                "empty" => new ProcessOutput(0, [], []),
                "malformed" => new ProcessOutput(0, Encoding.UTF8.GetBytes("-\n"), []),
                "zero" => new ProcessOutput(0, Encoding.UTF8.GetBytes("0\n"), []),
                "nonzero" => new ProcessOutput(1, [], Encoding.UTF8.GetBytes("stat failed\n")),
                _ => throw new InvalidOperationException(outcome),
            };
        });

        var result = fixture.RunWithRaw(runner);

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("birthtime_unknown", ReasonFor(result.Output, lane));
        Assert.Contains(runner.Invocations, invocation => invocation.FileName == "stat");
        Assert.Contains("\"removable_count\":0", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionBirthtimeAdapterAcceptsTrustedPositiveTimestamp()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/birthtime-trusted");
        var runner = fixture.CreateRunner();

        var result = fixture.RunWithRaw(runner);

        Assert.True(result.Success, result.Error);
        Assert.Equal("merged_clean", ReasonFor(result.Output, lane));
        var invocation = Assert.Single(
            runner.Invocations,
            candidate => candidate.FileName == "stat");
        if (OperatingSystem.IsMacOS())
        {
            Assert.Equal(["-f", "%B"], invocation.Arguments.Take(2).ToArray());
        }
        else
        {
            Assert.True(OperatingSystem.IsLinux());
            Assert.Equal(["-c", "%W"], invocation.Arguments.Take(2).ToArray());
        }
    }

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
        Assert.Contains(runner.Invocations, invocation => invocation.FileName == "stat");
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
