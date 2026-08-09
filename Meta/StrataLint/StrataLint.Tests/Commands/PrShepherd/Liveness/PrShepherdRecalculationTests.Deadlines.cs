using System.Diagnostics;

namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void InvalidDeadlineConfigurationFailsClosedBeforeExternalCalls()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.Run(
            environment: new Dictionary<string, string>
            {
                ["PR_SHEPHERD_API_TIMEOUT_SECONDS"] = "0",
            });

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(fixture.MutationCalls());
        Assert.Empty(fixture.BoundedCalls());
        Assert.Contains(
            "CONFIG_INVALID field=PR_SHEPHERD_API_TIMEOUT_SECONDS value=0",
            result.Error,
            StringComparison.Ordinal);
    }

    [Fact]
    public void WatchdogTimeoutKillsTheCommandProcessGroupIncludingGrandchildren()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(hangingTarget: "emit");
        var stopwatch = Stopwatch.StartNew();

        var result = fixture.Run(
            environment: new Dictionary<string, string>
            {
                ["PR_SHEPHERD_BUILD_TIMEOUT_SECONDS"] = "1",
                ["PR_SHEPHERD_SWEEP_TIMEOUT_SECONDS"] = "10",
                ["PR_SHEPHERD_KILL_GRACE_SECONDS"] = "1",
            });
        stopwatch.Stop();

        Assert.Equal(0, result.ExitCode);
        Assert.True(stopwatch.Elapsed < TimeSpan.FromSeconds(8), stopwatch.Elapsed.ToString());
        var failureState = fixture.RecalculationState(1);
        Assert.True(
            failureState.Contains("last_failure_class=emit.timeout", StringComparison.Ordinal),
            $"{failureState}\nlog:\n{result.Log}");
        Assert.Contains(
            "deadline_kind=build step=emit timeout_seconds=1 result=timeout",
            result.Log,
            StringComparison.Ordinal);
        var processIds = fixture.HangingProcessIds();
        Assert.True(processIds.Length >= 2, $"expected parent and grandchild pids, got {processIds.Length}");
        Assert.All(processIds, pid => Assert.False(fixture.IsProcessAlive(pid), $"pid {pid} survived timeout"));
    }

    [Fact]
    public void ChildExit124IsClassifiedAsExitRatherThanWatchdogTimeout()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingTarget: "emit", failingExitCode: 124);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        var state = fixture.RecalculationState(1);
        Assert.Contains("last_failure_class=emit.exit", state, StringComparison.Ordinal);
        Assert.Contains("failure_exit=124", state, StringComparison.Ordinal);
        Assert.DoesNotContain("emit.timeout", state, StringComparison.Ordinal);
    }

    [Fact]
    public void EveryNetworkAndBuildCallPublishesItsDeadlineReceipt()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var sweep = fixture.Run();
        Assert.Equal(0, sweep.ExitCode);
        Assert.True(
            fixture.MutationCalls().Contains("push", StringComparer.Ordinal),
            $"canonical chain did not push\nlog:\n{sweep.Log}\ncalls:\n{string.Join('\n', fixture.MutationCalls())}");
        var open = fixture.RunOpen(ghAppAvailable: true);
        Assert.Equal(0, open.ExitCode);
        var updateBranch = fixture.Run(expiryFingerprint: false);
        Assert.Equal(0, updateBranch.ExitCode);

        using var wakeFixture = new ShepherdFixture();
        wakeFixture.UseFixedClock(1_000);
        Assert.Equal(0, wakeFixture.Run(noChecks: true).ExitCode);
        wakeFixture.UseFixedClock(1_120);
        Assert.Equal(0, wakeFixture.Run(noChecks: true).ExitCode);

        using var watchFixture = new ShepherdFixture();
        Assert.Equal(0, watchFixture.RunWatch().ExitCode);

        var calls = fixture.BoundedCalls()
            .Concat(wakeFixture.BoundedCalls())
            .Concat(watchFixture.BoundedCalls())
            .ToArray();
        AssertBounded(calls, "api", "graphql-remaining", "120");
        AssertBounded(calls, "api", "pr-list", "120");
        AssertBounded(calls, "api", "pr-diff", "120");
        AssertBounded(calls, "api", "run-view", "120");
        AssertBounded(calls, "git", "dev-oid", "300");
        AssertBounded(calls, "build", "worktree", "1800");
        AssertBounded(calls, "git", "reset", "300");
        AssertBounded(calls, "git", "clean", "300");
        AssertBounded(calls, "git", "fetch", "300");
        AssertBounded(calls, "git", "checkout", "300");
        AssertBounded(calls, "git", "merge", "300");
        AssertBounded(calls, "build", "lean-report", "1800");
        AssertBounded(calls, "build", "emit", "1800");
        AssertBounded(calls, "build", "ingest", "1800");
        AssertBounded(calls, "build", "echo-verify", "1800");
        AssertBounded(calls, "build", "ledger-append", "1800");
        AssertBounded(calls, "build", "emit-check", "1800");
        AssertBounded(calls, "git", "add", "300");
        AssertBounded(calls, "git", "commit", "300");
        AssertBounded(calls, "git", "push", "300");
        AssertBounded(calls, "api", "gh-app-token", "120");
        AssertBounded(calls, "api", "pr-create", "120");
        AssertBounded(calls, "api", "pr-auto-merge", "120");
        AssertBounded(calls, "api", "update-branch", "120");
        AssertBounded(calls, "api", "wake-close", "120");
        AssertBounded(calls, "api", "wake-reopen", "120");
        AssertBounded(calls, "api", "wake-rearm", "120");
        AssertBounded(calls, "api", "armed-pr-count", "120");
        Assert.DoesNotContain(
            calls,
            call => call.Split('|', 4) is var fields
                && fields.Length >= 3
                && (string.IsNullOrEmpty(fields[1]) || string.IsNullOrEmpty(fields[2])));
    }

    private static void AssertBounded(
        IEnumerable<string> calls,
        string kind,
        string step,
        string timeoutSeconds) =>
        Assert.Contains(
            calls,
            call => call.StartsWith($"{kind}|{step}|{timeoutSeconds}|", StringComparison.Ordinal));

}
