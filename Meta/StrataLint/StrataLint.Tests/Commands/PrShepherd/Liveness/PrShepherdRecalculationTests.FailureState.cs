namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void RepeatedFailureBacksOffThenOpensAndLetsTheNextFifoItemRun()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingTarget: "emit-check", failingPr: 1);

        fixture.UseFixedClock(1_000);
        var first = fixture.Run();
        Assert.Equal(0, first.ExitCode);
        Assert.Contains("class_attempts=1\n", fixture.RecalculationState(1));
        Assert.Contains("total_attempts=1\n", fixture.RecalculationState(1));
        Assert.Contains("next_at=1480\n", fixture.RecalculationState(1));
        Assert.Contains("terminal=0\n", fixture.RecalculationState(1));

        fixture.ClearMutationCalls();
        fixture.UseFixedClock(1_001);
        var backedOff = fixture.Run();
        Assert.Equal(0, backedOff.ExitCode);
        Assert.Empty(fixture.MutationCalls());
        Assert.Contains(
            "RECALC_BACKOFF pr=#1 failure_class=emit-check.exit attempts=1 next_at=1480 now=1001",
            backedOff.Log,
            StringComparison.Ordinal);

        fixture.UseFixedClock(1_480);
        var second = fixture.Run();
        Assert.Equal(0, second.ExitCode);
        Assert.Contains("class_attempts=2\n", fixture.RecalculationState(1));
        Assert.Contains("total_attempts=2\n", fixture.RecalculationState(1));
        Assert.Contains("next_at=3400\n", fixture.RecalculationState(1));

        fixture.UseFixedClock(3_400);
        var terminal = fixture.Run();
        Assert.Equal(0, terminal.ExitCode);
        var state = fixture.RecalculationState(1);
        Assert.Contains("schema=pr-recalculation-state-v1\n", state);
        Assert.Contains("pr=1\n", state);
        Assert.Contains($"head_oid={fixture.OriginalHead}\n", state);
        Assert.Contains($"dev_oid={fixture.BaseHead}\n", state);
        Assert.Matches("script_blob=[0-9a-f]{40}\\n", state);
        Assert.Contains("last_failure_class=emit-check.exit\n", state);
        Assert.Contains("class_attempts=3\n", state);
        Assert.Contains("total_attempts=3\n", state);
        Assert.Contains("terminal=1\n", state);
        Assert.Contains(
            "ALERT #1 RECALC_OPEN failure_class=emit-check.exit class_attempts=3 total_attempts=3 terminal=OPEN",
            terminal.Log,
            StringComparison.Ordinal);
        Assert.False(fixture.DerivedLeaseExists);

        fixture.SetFailingTarget("");
        fixture.ClearMutationCalls();
        fixture.UseFixedClock(3_401);
        var nextItem = fixture.Run(twoDerivedPrRows: true);
        Assert.Equal(0, nextItem.ExitCode);
        Assert.Contains("RECALC_OPEN pr=#1", nextItem.Log, StringComparison.Ordinal);
        Assert.Contains("FIFO LEASE acquired pr=#2", nextItem.Log, StringComparison.Ordinal);
        Assert.Contains("push", fixture.MutationCalls());
    }

    [Fact]
    public void AlternatingFailureClassesCannotEscapeTheTotalAttemptCap()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingTarget: "emit", failingPr: 1);
        var times = new[] { 1_000L, 1_480L, 1_960L, 2_440L, 2_920L };

        for (var index = 0; index < times.Length; index++)
        {
            fixture.SetFailingTarget(index % 2 == 0 ? "emit" : "emit-check");
            fixture.UseFixedClock(times[index]);
            var result = fixture.Run();
            Assert.Equal(0, result.ExitCode);
        }

        var state = fixture.RecalculationState(1);
        Assert.Contains("class_attempts=1\n", state);
        Assert.Contains("total_attempts=5\n", state);
        Assert.Contains("terminal=1\n", state);
    }

    [Fact]
    public void ConfirmedDevIdentityChangeResetsFailureHistoryBeforeHalfOpenProbe()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingTarget: "emit-check", failingPr: 1);

        fixture.UseFixedClock(1_000);
        var first = fixture.Run();
        Assert.Equal(0, first.ExitCode);
        Assert.Contains("total_attempts=1\n", fixture.RecalculationState(1));

        fixture.AdvanceDev();
        fixture.UseFixedClock(1_001);
        var reset = fixture.Run();

        Assert.Equal(0, reset.ExitCode);
        Assert.Contains(
            "RECALC_RESET pr=#1 reason=work-identity-changed",
            reset.Log,
            StringComparison.Ordinal);
        var halfOpen = fixture.Run();
        Assert.Equal(0, halfOpen.ExitCode);
        var state = fixture.RecalculationState(1);
        Assert.Contains($"dev_oid={fixture.BaseHead}\n", state);
        Assert.Contains("total_attempts=1\n", state);
    }

    [Fact]
    public void InfrastructureFailureUsesBoundedBackoffAndThenHalfOpenProbe()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingGhOperation: "pr list");

        fixture.UseFixedClock(1_000);
        var failed = fixture.Run();
        Assert.NotEqual(0, failed.ExitCode);
        Assert.True(fixture.InfrastructureStateExists);
        Assert.Contains(
            "INFRA_FAILURE failure_class=pr-list.exit attempts=1 next_at=1120",
            failed.Log,
            StringComparison.Ordinal);

        fixture.ClearBoundedCalls();
        fixture.UseFixedClock(1_001);
        var backedOff = fixture.Run();
        Assert.Equal(0, backedOff.ExitCode);
        Assert.Empty(fixture.BoundedCalls());
        Assert.Contains(
            "INFRA_BACKOFF failure_class=pr-list.exit attempts=1 next_at=1120 now=1001",
            backedOff.Log,
            StringComparison.Ordinal);

        fixture.SetFailingGhOperation("");
        fixture.UseFixedClock(1_120);
        var probe = fixture.Run();
        Assert.Equal(0, probe.ExitCode);
        Assert.False(fixture.InfrastructureStateExists);
        Assert.Contains("INFRA_HALF_OPEN", probe.Log, StringComparison.Ordinal);
        Assert.Contains("push", fixture.MutationCalls());
    }
}
