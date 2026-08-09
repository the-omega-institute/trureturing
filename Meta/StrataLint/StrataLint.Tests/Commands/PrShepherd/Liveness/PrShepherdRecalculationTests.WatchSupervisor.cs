using System.Text.Json;

namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void WatchSupervisorRestartsNoOwnerExactlyOnce()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var dead = fixture.RunStatus();
        Assert.Equal(2, dead.ExitCode);
        Assert.StartsWith("status=dead reason=no-owner ", dead.Output, StringComparison.Ordinal);

        var supervised = fixture.RunSupervisor();

        Assert.Equal(0, supervised.ExitCode);
        fixture.WaitForWatchPhase("waiting");
        Assert.Equal(0, fixture.RunStatus().ExitCode);
        AssertDecision(
            fixture.WatchRestartDecisions(),
            action: "restart",
            decisionReason: "verified-owner-gone",
            statusExit: 2,
            statusReason: "no-owner",
            ownerStatus: "no-owner");
    }

    [Fact]
    public void WatchSupervisorRestartsGoneOwnerExactlyOnce()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        Assert.Equal(0, fixture.RunStart().ExitCode);
        fixture.WaitForWatchPhase("waiting");
        var formerOwner = fixture.ReadOwnerPid();
        fixture.StopWatch(formerOwner);
        var dead = fixture.RunStatus();
        Assert.Equal(2, dead.ExitCode);
        Assert.StartsWith("status=dead reason=owner-gone ", dead.Output, StringComparison.Ordinal);

        var supervised = fixture.RunSupervisor();

        Assert.Equal(0, supervised.ExitCode);
        fixture.WaitForWatchPhase("waiting");
        var replacementOwner = fixture.ReadOwnerPid();
        Assert.NotEqual(formerOwner, replacementOwner);
        Assert.True(fixture.IsProcessAlive(replacementOwner));
        AssertDecision(
            fixture.WatchRestartDecisions(),
            action: "restart",
            decisionReason: "verified-owner-gone",
            statusExit: 2,
            statusReason: "owner-gone",
            ownerStatus: "owner-gone");
    }

    [Fact]
    public void WatchSupervisorRefusesTerminalStateUntilOwnerIsGone()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        Assert.Equal(0, fixture.RunStart().ExitCode);
        fixture.WaitForWatchPhase("waiting");
        var owner = fixture.ReadOwnerPid();
        fixture.ReplaceWatchStateField("phase", "terminal");
        fixture.ReplaceWatchStateField("terminal_exit", "0");
        var dead = fixture.RunStatus();
        Assert.Equal(2, dead.ExitCode);
        Assert.StartsWith("status=dead reason=terminal ", dead.Output, StringComparison.Ordinal);

        var supervised = fixture.RunSupervisor();

        Assert.Equal(1, supervised.ExitCode);
        Assert.Equal(owner, fixture.ReadOwnerPid());
        Assert.True(fixture.IsProcessAlive(owner));
        AssertDecision(
            fixture.WatchRestartDecisions(),
            action: "refuse",
            decisionReason: "owner-live",
            statusExit: 2,
            statusReason: "terminal",
            ownerStatus: "live");
    }

    [Fact]
    public void WatchSupervisorRefusesUnverifiableOwnerWithoutRestart()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        Assert.Equal(0, fixture.RunStart().ExitCode);
        fixture.WaitForWatchPhase("waiting");
        var owner = fixture.ReadOwnerPid();
        fixture.CorruptWatchOwner();
        var stalled = fixture.RunStatus();
        Assert.Equal(1, stalled.ExitCode);
        Assert.StartsWith(
            "status=stalled reason=owner-unverifiable ",
            stalled.Output,
            StringComparison.Ordinal);

        var supervised = fixture.RunSupervisor();

        Assert.Equal(1, supervised.ExitCode);
        Assert.True(fixture.IsProcessAlive(owner));
        Assert.Equal(1, fixture.RunStatus().ExitCode);
        AssertDecision(
            fixture.WatchRestartDecisions(),
            action: "refuse",
            decisionReason: "stalled",
            statusExit: 1,
            statusReason: "owner-unverifiable",
            ownerStatus: "unverifiable");
    }

    [Fact]
    public void WatchSupervisorCapsFailedRestartsAtSharedBackoffBoundary()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        Assert.Equal(0, fixture.RunStart().ExitCode);
        fixture.WaitForWatchPhase("waiting");
        var owner = fixture.ReadOwnerPid();
        fixture.RemoveWatchOwner();

        var supervised = fixture.RunSupervisor();

        Assert.Equal(1, supervised.ExitCode);
        Assert.True(fixture.IsProcessAlive(owner));
        var decisions = fixture.WatchRestartDecisions()
            .Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.Equal(3, decisions.Length);
        for (var index = 0; index < decisions.Length; index++)
        {
            using var document = JsonDocument.Parse(decisions[index]);
            Assert.Equal("restart", document.RootElement.GetProperty("action").GetString());
            Assert.Equal(index + 1, document.RootElement.GetProperty("attempt").GetInt32());
            Assert.Equal(3, document.RootElement.GetProperty("max_attempts").GetInt32());
        }
        Assert.Contains(
            "WATCH supervisor retryable step=start attempt=1/3 start_exit=1 retry_in_seconds=1",
            supervised.Log,
            StringComparison.Ordinal);
        Assert.Contains(
            "WATCH supervisor retryable step=start attempt=2/3 start_exit=1 retry_in_seconds=2",
            supervised.Log,
            StringComparison.Ordinal);
        Assert.Contains(
            "WATCH supervisor exhausted class=retryable step=start attempt=3/3 start_exit=1",
            supervised.Log,
            StringComparison.Ordinal);
    }

    private static void AssertDecision(
        string artifact,
        string action,
        string decisionReason,
        int statusExit,
        string statusReason,
        string ownerStatus)
    {
        var lines = artifact.Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.Single(lines);
        using var document = JsonDocument.Parse(lines[0]);
        var decision = document.RootElement;
        Assert.Equal("pr-watch-restart-decision-v1", decision.GetProperty("schema").GetString());
        Assert.Equal(action, decision.GetProperty("action").GetString());
        Assert.Equal(decisionReason, decision.GetProperty("decision_reason").GetString());
        Assert.Equal(statusExit, decision.GetProperty("status_exit").GetInt32());
        Assert.Equal(statusReason, decision.GetProperty("status_reason").GetString());
        Assert.Equal(ownerStatus, decision.GetProperty("owner_status").GetString());
        Assert.Equal(1, decision.GetProperty("attempt").GetInt32());
        Assert.Equal(3, decision.GetProperty("max_attempts").GetInt32());
    }
}
