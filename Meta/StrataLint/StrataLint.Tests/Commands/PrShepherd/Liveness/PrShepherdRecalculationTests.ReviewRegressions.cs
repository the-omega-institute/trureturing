namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void SweepDeadlineLeavesClassifiedStateAndReleasesItsDerivedLease()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(hangingTarget: "emit");

        var result = fixture.Run(
            environment: new Dictionary<string, string>
            {
                ["PR_SHEPHERD_BUILD_TIMEOUT_SECONDS"] = "10",
                ["PR_SHEPHERD_SWEEP_TIMEOUT_SECONDS"] = "3",
                ["PR_SHEPHERD_KILL_GRACE_SECONDS"] = "1",
            });

        Assert.True(
            result.ExitCode is 0 or 1,
            $"exit={result.ExitCode}\nstdout:\n{result.Output}\nstderr:\n{result.Error}\nlog:\n{result.Log}");
        if (fixture.RecalculationStateExists(1))
        {
            Assert.Matches("last_failure_class=[a-z0-9-]+\\.timeout", fixture.RecalculationState(1));
        }
        else
        {
            Assert.True(fixture.InfrastructureStateExists, result.Log);
            Assert.Matches("failure_class=[a-z0-9-]+\\.timeout", fixture.InfrastructureState());
        }
        Assert.False(fixture.DerivedLeaseExists);
    }

    [Fact]
    public void NonNonFastForwardPushFailureEntersTheRecalculationStateMachine()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingTarget: "push", failingExitCode: 88);
        fixture.UseFixedClock(1_000);

        var first = fixture.Run();
        fixture.UseFixedClock(1_001);
        var second = fixture.Run();

        Assert.Equal(0, first.ExitCode);
        Assert.Equal(0, second.ExitCode);
        Assert.Equal(1, fixture.MutationCalls().Count(call => call == "push"));
        Assert.Contains("last_failure_class=push.exit", fixture.RecalculationState(1));
        Assert.Contains("class_attempts=1", fixture.RecalculationState(1));
        Assert.DoesNotContain("非 FF", first.Log, StringComparison.Ordinal);
        Assert.Contains("RECALC_BACKOFF pr=#1 failure_class=push.exit", second.Log);
    }

    [Fact]
    public void TrackedHelperChangeResetsTerminalRecalculationIdentity()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingTarget: "emit-check", failingPr: 1);
        foreach (var timestamp in new[] { 1_000L, 1_480L, 3_400L })
        {
            fixture.UseFixedClock(timestamp);
            Assert.Equal(0, fixture.RunTrackedSweep().ExitCode);
        }
        Assert.Contains("terminal=1", fixture.RecalculationState(1));

        fixture.CommitTrackedHelperChange("change-actions-identity");
        fixture.UseFixedClock(3_401);
        var probe = fixture.RunTrackedSweep();

        Assert.Equal(0, probe.ExitCode);
        Assert.Contains("RECALC_RESET pr=#1 reason=work-identity-changed", probe.Log);
        Assert.Contains("total_attempts=1", fixture.RecalculationState(1));
    }

    [Fact]
    public void TrackedLedgerHelperChangeResetsTerminalRecalculationIdentity()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingTarget: "emit-check", failingPr: 1);
        foreach (var timestamp in new[] { 1_000L, 1_480L, 3_400L })
        {
            fixture.UseFixedClock(timestamp);
            Assert.Equal(0, fixture.RunTrackedSweep().ExitCode);
        }
        Assert.Contains("terminal=1", fixture.RecalculationState(1));

        fixture.CommitTrackedLedgerHelperChange("change-ledger-identity");
        fixture.UseFixedClock(3_401);
        var probe = fixture.RunTrackedSweep();

        Assert.Equal(0, probe.ExitCode);
        Assert.Contains("RECALC_RESET pr=#1 reason=work-identity-changed", probe.Log);
        Assert.Contains("total_attempts=1", fixture.RecalculationState(1));
    }

    [Fact]
    public void FailedWatchSweepPublishesFailureInsteadOfSweepComplete()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingGhOperation: "pr list");

        var started = fixture.RunStart();
        Assert.Equal(0, started.ExitCode);
        fixture.WaitForWatchPhase("waiting");

        var state = fixture.WatchState();
        Assert.Contains("last_outcome=sweep-exit", state);
        Assert.DoesNotContain("last_outcome=sweep-complete", state);
        fixture.StopWatch();
    }

    [Fact]
    public void TermInterruptsTheActiveBoundedTreeAndRunsCleanupPromptly()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(hangingTarget: "emit");
        var started = fixture.RunStart(
            dryRun: false,
            environment: new Dictionary<string, string>
            {
                ["PR_SHEPHERD_BUILD_TIMEOUT_SECONDS"] = "30",
                ["PR_SHEPHERD_SWEEP_TIMEOUT_SECONDS"] = "20",
                ["PR_SHEPHERD_KILL_GRACE_SECONDS"] = "1",
            });
        Assert.Equal(0, started.ExitCode);
        fixture.WaitForHangingProcesses();

        var elapsed = fixture.TerminateWatch(TimeSpan.FromSeconds(8));

        Assert.True(elapsed < TimeSpan.FromSeconds(3), elapsed.ToString());
        Assert.All(fixture.HangingProcessIds(), pid => Assert.False(fixture.IsProcessAlive(pid)));
        Assert.False(fixture.DerivedLeaseExists);
        Assert.Contains("terminal_exit=143", fixture.WatchState());
    }

    [Fact]
    public void NestedGitStageRestoresARealParentDeadlineInsteadOfCompletedFetch()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var started = fixture.RunStart(
            dryRun: false,
            environment: new Dictionary<string, string>
            {
                ["PR_TEST_HANG_GIT_OPERATION"] = "checkout",
                ["PR_SHEPHERD_SWEEP_TIMEOUT_SECONDS"] = "30",
                ["PR_SHEPHERD_KILL_GRACE_SECONDS"] = "1",
            });
        Assert.Equal(0, started.ExitCode);
        fixture.WaitForHangingProcesses();

        var state = fixture.WatchState();
        Assert.Contains("current_step=checkout", state);
        Assert.DoesNotContain("step_deadline_at=0", state);
        fixture.TerminateWatch(TimeSpan.FromSeconds(8));
    }

    [Fact]
    public void CurrentOwnerIsCheckedBeforeAnOldTerminalSnapshot()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var started = fixture.RunStart();
        Assert.Equal(0, started.ExitCode);
        fixture.WaitForWatchPhase("waiting");
        fixture.ReplaceWatchStateField("terminal_exit", "9");
        fixture.ReplaceWatchStateField("phase", "terminal");
        fixture.ReplaceWatchOwner(Environment.ProcessId);

        var status = fixture.RunStatus();

        Assert.Equal(1, status.ExitCode);
        Assert.StartsWith("status=stalled reason=state-unverifiable ", status.Output);
        fixture.StopWatch();
    }

    [Fact]
    public void DeadStatusKeepsTheLastProgressReading()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var started = fixture.RunStart();
        Assert.Equal(0, started.ExitCode);
        fixture.WaitForWatchPhase("waiting");
        fixture.RemoveWatchOwner();

        var status = fixture.RunStatus();

        Assert.Equal(2, status.ExitCode);
        Assert.Contains("last_progress_at=", status.Output);
        fixture.StopWatch();
    }

    [Fact]
    public async Task InfrastructureHalfOpenAllowsOnlyOneConcurrentProbe()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingGhOperation: "pr list");
        fixture.UseFixedClock(1_000);
        Assert.NotEqual(0, fixture.Run().ExitCode);
        fixture.SetFailingGhOperation("");
        fixture.ClearBoundedCalls();
        fixture.UseFixedClock(1_120);
        var environment = new Dictionary<string, string>
        {
            ["PR_TEST_PAUSE_GH_OPERATION"] = "pr list",
        };

        var probes = new[]
        {
            Task.Factory.StartNew(
                () => fixture.Run(environment: environment),
                CancellationToken.None,
                TaskCreationOptions.LongRunning,
                TaskScheduler.Default),
            Task.Factory.StartNew(
                () => fixture.Run(environment: environment),
                CancellationToken.None,
                TaskCreationOptions.LongRunning,
                TaskScheduler.Default),
        };
        var results = await Task.WhenAll(probes);

        var calls = fixture.BoundedCalls();
        var probeCount = calls.Count(call => call.StartsWith("api|pr-list|", StringComparison.Ordinal));
        Assert.True(
            probeCount == 1,
            $"expected one half-open probe, got {probeCount}\n"
            + $"calls:\n{string.Join('\n', calls)}\n"
            + $"logs:\n{string.Join("\n---\n", results.Select(result => result.Log))}");
    }
}
