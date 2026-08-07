namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void StatusReportsAliveStalledAndDeadFromOwnerAndProgressState()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var started = fixture.RunStart();
        Assert.Equal(0, started.ExitCode);
        fixture.WaitForWatchPhase("waiting");

        var alive = fixture.RunStatus();
        Assert.Equal(0, alive.ExitCode);
        Assert.StartsWith("status=alive ", alive.Output, StringComparison.Ordinal);
        Assert.Single(alive.Output.Split('\n', StringSplitOptions.RemoveEmptyEntries));

        var state = fixture.WatchState();
        Assert.StartsWith("schema=pr-watch-state-v2\n", state, StringComparison.Ordinal);
        Assert.Contains("phase=", state, StringComparison.Ordinal);
        Assert.Contains("current_pr=", state, StringComparison.Ordinal);
        Assert.Contains("current_step=", state, StringComparison.Ordinal);
        Assert.Contains("step_started_at=", state, StringComparison.Ordinal);
        Assert.Contains("step_deadline_at=", state, StringComparison.Ordinal);
        Assert.Contains("last_progress_at=", state, StringComparison.Ordinal);
        Assert.Contains("last_outcome=", state, StringComparison.Ordinal);
        Assert.Contains("cycle=1\n", state, StringComparison.Ordinal);
        Assert.Contains("terminal_exit=none\n", state, StringComparison.Ordinal);
        var fields = state.Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Select(line => line.Split('=', 2))
            .ToDictionary(parts => parts[0], parts => parts[1], StringComparer.Ordinal);
        Assert.NotEqual(fields["last_progress_at"], fields["step_deadline_at"]);

        fixture.ReplaceWatchStateField("step_deadline_at", "1");
        var stalled = fixture.RunStatus();
        Assert.Equal(1, stalled.ExitCode);
        Assert.StartsWith(
            "status=stalled reason=deadline-exceeded ",
            stalled.Output,
            StringComparison.Ordinal);

        fixture.StopWatch();
        var dead = fixture.RunStatus();
        Assert.Equal(2, dead.ExitCode);
        Assert.StartsWith("status=dead ", dead.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void UnverifiableLiveOwnerIsStalledRatherThanAliveOrDead()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var started = fixture.RunStart();
        Assert.Equal(0, started.ExitCode);
        var ownerPid = fixture.ReadOwnerPid();
        fixture.CorruptWatchOwner();

        var status = fixture.RunStatus();

        Assert.Equal(1, status.ExitCode);
        Assert.StartsWith(
            "status=stalled reason=owner-unverifiable ",
            status.Output,
            StringComparison.Ordinal);
        fixture.StopWatch(ownerPid);
    }
}
