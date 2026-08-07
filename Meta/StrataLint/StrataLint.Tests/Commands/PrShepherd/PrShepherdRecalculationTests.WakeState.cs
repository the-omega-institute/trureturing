namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void QueuedInProgressAndPendingRollupsSuppressWakeWithoutRunListQuery()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        fixture.UseFixedClock(1_000);

        var first = fixture.Run(statusRollupCount: 0);
        fixture.UseFixedClock(1_120);
        var due = fixture.Run(statusRollupCount: 3);
        fixture.UseFixedClock(10_000);
        var later = fixture.Run(statusRollupCount: 3);

        Assert.Equal(0, first.ExitCode);
        Assert.Equal(0, due.ExitCode);
        Assert.Equal(0, later.ExitCode);
        Assert.Empty(fixture.MutationCalls());
        Assert.True(fixture.WakeStateExists());
        Assert.Contains("count=0\n", fixture.WakeState(), StringComparison.Ordinal);
        Assert.Contains("next_at=1120\n", fixture.WakeState(), StringComparison.Ordinal);
        var scripts = ReadShepherdScripts();
        Assert.Contains("(.statusCheckRollup|length)", scripts, StringComparison.Ordinal);
        Assert.DoesNotContain("run list", scripts, StringComparison.Ordinal);
    }

    [Fact]
    public void ChecklessHeadUsesPersistentExponentialBackoffAcrossProcesses()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        RunChecklessAt(fixture, 1_000);
        RunChecklessAt(fixture, 1_119);
        Assert.Empty(fixture.MutationCalls());

        RunChecklessAt(fixture, 1_120);
        RunChecklessAt(fixture, 1_599);
        Assert.Single(fixture.MutationCalls(), IsWakeClose);

        RunChecklessAt(fixture, 1_600);

        Assert.Equal(2, fixture.MutationCalls().Count(IsWakeClose));
        Assert.Contains("count=2\n", fixture.WakeState(), StringComparison.Ordinal);
        Assert.Contains("next_at=3520\n", fixture.WakeState(), StringComparison.Ordinal);
    }

    [Fact]
    public void SuccessfulWakeRetainsHistoricalStateMarker()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        RunChecklessAt(fixture, 1_000);
        RunChecklessAt(fixture, 1_120);

        Assert.Single(fixture.MutationCalls(), IsWakeClose);
        Assert.Contains($"head={fixture.OriginalHead}\n", fixture.WakeState(), StringComparison.Ordinal);
        Assert.Contains("count=1\n", fixture.WakeState(), StringComparison.Ordinal);
        Assert.Contains("next_at=1600\n", fixture.WakeState(), StringComparison.Ordinal);
        Assert.Contains("terminal=0\n", fixture.WakeState(), StringComparison.Ordinal);
    }

    [Fact]
    public void NewHeadResetsWakeHistoryBeforeRetrying()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        RunChecklessAt(fixture, 1_000);
        RunChecklessAt(fixture, 1_120);
        fixture.MoveHeadToAttacker();
        RunChecklessAt(fixture, 1_121);

        Assert.Single(fixture.MutationCalls(), IsWakeClose);
        Assert.Contains($"head={fixture.AttackerHead}\n", fixture.WakeState(), StringComparison.Ordinal);
        Assert.Contains("count=0\n", fixture.WakeState(), StringComparison.Ordinal);
        Assert.Contains("next_at=1241\n", fixture.WakeState(), StringComparison.Ordinal);

        RunChecklessAt(fixture, 1_241);

        Assert.Equal(2, fixture.MutationCalls().Count(IsWakeClose));
        Assert.Contains("count=1\n", fixture.WakeState(), StringComparison.Ordinal);
    }

    [Fact]
    public void ThirdWakeOpensGreppableTerminalAlertAndNeverWakesHeadAgain()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        RunChecklessAt(fixture, 1_000);
        RunChecklessAt(fixture, 1_120);
        RunChecklessAt(fixture, 1_600);
        var capped = RunChecklessAt(fixture, 3_520);
        var afterCap = RunChecklessAt(fixture, 100_000);

        Assert.Equal(3, fixture.MutationCalls().Count(IsWakeClose));
        Assert.Contains("count=3\n", fixture.WakeState(), StringComparison.Ordinal);
        Assert.Contains("terminal=1\n", fixture.WakeState(), StringComparison.Ordinal);
        Assert.Contains(
            $"ALERT #1 WAKE_CAP head={fixture.OriginalHead} count=3 max=3 terminal=OPEN",
            capped.Log,
            StringComparison.Ordinal);
        Assert.Equal(3, fixture.MutationCalls().Count(IsWakeClose));
        Assert.Contains("terminal=OPEN", afterCap.Log, StringComparison.Ordinal);
    }

    private static ShepherdResult RunChecklessAt(ShepherdFixture fixture, long epochSeconds)
    {
        fixture.UseFixedClock(epochSeconds);
        var result = fixture.Run(statusRollupCount: 0);
        Assert.Equal(0, result.ExitCode);
        return result;
    }

    private static bool IsWakeClose(string call) =>
        call.StartsWith("gh:pr close 1 ", StringComparison.Ordinal);
}
