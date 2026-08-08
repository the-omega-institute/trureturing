using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void NewlyDiscoveredSourcedHelperChangesTheWorkIdentity()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingTarget: "emit-check", failingPr: 1);
        fixture.CommitNewTrackedHelper("initial-extra-helper");
        var environment = new Dictionary<string, string>
        {
            ["PR_TEST_EXTRA_HELPER_LOADS"] = fixture.ExtraHelperLoadsPath,
        };
        foreach (var timestamp in new[] { 1_000L, 1_480L, 3_400L })
        {
            fixture.UseFixedClock(timestamp);
            Assert.Equal(0, fixture.RunTrackedSweep(environment).ExitCode);
        }
        Assert.Contains("terminal=1", fixture.RecalculationState(1));

        fixture.CommitTrackedExtraHelperChange("changed-extra-helper");
        fixture.UseFixedClock(3_401);
        var probe = fixture.RunTrackedSweep(environment);

        Assert.Equal(0, probe.ExitCode);
        Assert.True(File.Exists(fixture.ExtraHelperLoadsPath), "the discovered helper was not sourced");
        Assert.True(
            probe.Log.Contains(
                "RECALC_RESET pr=#1 reason=work-identity-changed",
                StringComparison.Ordinal),
            $"state:\n{fixture.RecalculationState(1)}\nlog:\n{probe.Log}\n"
            + $"bounded calls:\n{string.Join('\n', fixture.BoundedCalls())}");
        Assert.Contains("total_attempts=1", fixture.RecalculationState(1));
    }

    [Fact]
    public void OldDerivedLeaseOwnerCannotDeleteAReplacementLease()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.RunDerivedLeaseReleaseInterleaving();

        Assert.True(
            result.ExitCode == 0,
            $"exit={result.ExitCode}\nstdout:\n{result.Output}\nstderr:\n{result.Error}");
        Assert.Equal("new-owner-token\n", result.Output);
    }

    [Fact]
    public void BootstrapReloadGitTimeoutReapsTheEntireHangingTree()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.RunStart(
            environment: new Dictionary<string, string>
            {
                ["PR_TEST_HANG_GIT_OPERATION"] = "rev-parse --show-toplevel",
                ["PR_SHEPHERD_API_TIMEOUT_SECONDS"] = "5",
                ["PR_SHEPHERD_GIT_TIMEOUT_SECONDS"] = "1",
                ["PR_SHEPHERD_KILL_GRACE_SECONDS"] = "1",
            });
        var processIds = fixture.HangingProcessIds();
        var survivors = processIds.Where(fixture.IsProcessAlive).ToArray();
        fixture.KillProcesses(processIds);

        Assert.Equal(1, result.ExitCode);
        Assert.True(processIds.Length >= 2, $"expected hanging git parent and child, got {processIds.Length}");
        Assert.Empty(survivors);
        Assert.Contains(
            "deadline_kind=git step=watch-reload-root timeout_seconds=1 result=timeout",
            result.Log,
            StringComparison.Ordinal);
        Assert.Contains(
            fixture.BoundedCalls(),
            call => call.StartsWith("git|watch-reload-root|1|", StringComparison.Ordinal));
    }

    [Fact]
    public void BootstrapFreshnessRejectionPreservesExitAndPublishesTerminalState()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        fixture.DirtyTrackedActionsHelper("bootstrap-freshness-rejection");

        var result = fixture.RunWatch();

        Assert.Equal(1, result.ExitCode);
        Assert.DoesNotContain("command not found", result.Error, StringComparison.Ordinal);
        Assert.True(File.Exists(fixture.WatchStatePath), "bootstrap failure did not publish state");
        Assert.Contains("phase=terminal\n", fixture.WatchState());
        Assert.Contains("last_outcome=bootstrap-exit\n", fixture.WatchState());
        Assert.Contains("terminal_exit=1\n", fixture.WatchState());
    }

    private sealed partial class ShepherdFixture
    {
        private const string ExtraHelperPath =
            "Meta/StrataLint/scripts/shepherd/pr-shepherd-review-probe.sh";

        internal string ExtraHelperLoadsPath => Path.Combine(temporary.Path, "extra-helper-loads");

        internal void CommitNewTrackedHelper(string marker)
        {
            EnsureTrackedWatchScripts();
            Write(
                repository,
                ExtraHelperPath,
                "if [[ -n \"${PR_TEST_EXTRA_HELPER_LOADS:-}\" ]]; then\n"
                + "  printf 'loaded\\n' >> \"$PR_TEST_EXTRA_HELPER_LOADS\"\n"
                + "fi\n"
                + $"# {marker}\n");
            Git(repository, "add", ExtraHelperPath);
            Git(repository, "commit", "-m", marker);
        }

        internal void CommitTrackedExtraHelperChange(string marker)
        {
            File.AppendAllText(
                Path.Combine(repository, ExtraHelperPath),
                $"# {marker}\n",
                new UTF8Encoding(false));
            Git(repository, "add", ExtraHelperPath);
            Git(repository, "commit", "-m", marker);
        }

        internal void DirtyTrackedActionsHelper(string marker)
        {
            EnsureTrackedWatchScripts();
            File.AppendAllText(
                Path.Combine(repository, ShepherdActionsScriptPath),
                $"# {marker}\n",
                new UTF8Encoding(false));
        }

        internal CommandResult RunDerivedLeaseReleaseInterleaving()
        {
            EnsureTrackedWatchScripts();
            var leaseDirectory = Path.Combine(StateDirectory, "derived-fifo.lease");
            Directory.CreateDirectory(leaseDirectory);
            File.WriteAllText(
                Path.Combine(leaseDirectory, "owner"),
                "schema=derived-fifo-lease-v1\n"
                + "pr=1\n"
                + "acquired_at=1000\n"
                + "token=old-owner-token\n",
                new UTF8Encoding(false));
            var module = Path.Combine(repository, ShepherdLeaseScriptPath);
            const string script = """
                set -euo pipefail
                DERIVED_LEASE_OBSERVED_TOKEN=""
                DERIVED_LEASE_TOKEN=""
                DERIVED_LEASE_PR=""
                log() { :; }
                source "$PR_TEST_LEASE_MODULE"
                inject_replacement_lease() {
                  trap - DEBUG
                  race_injected=1
                  /bin/mv "$STATE_DIR/derived-fifo.lease" "$STATE_DIR/expired-old-lease"
                  /bin/mkdir "$STATE_DIR/derived-fifo.lease"
                  printf 'schema=derived-fifo-lease-v1\npr=2\nacquired_at=1001\ntoken=new-owner-token\n' \
                    > "$STATE_DIR/derived-fifo.lease/owner"
                }
                schedule_release_race() {
                  if [[ "$race_injected" == 0 ]]; then
                    case "$BASH_COMMAND" in
                      'rm -f "$directory/owner"'|'mv "$directory" '*) inject_replacement_lease ;;
                    esac
                  fi
                }
                race_injected=0
                set -T
                trap schedule_release_race DEBUG
                release_derived_lease_token old-owner-token 1
                trap - DEBUG
                DERIVED_LEASE_OBSERVED_TOKEN=""
                if ! load_derived_lease "$STATE_DIR/derived-fifo.lease"; then
                  printf 'new_lease=deleted_by_old_owner\n'
                  exit 1
                fi
                printf '%s\n' "$DERIVED_LEASE_OBSERVED_TOKEN"
                """;
            var result = BoundedProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"STATE_DIR={StateDirectory}",
                    "DRYRUN=0",
                    $"PR_TEST_LEASE_MODULE={module}",
                    "/bin/bash",
                    "-c",
                    script,
                ],
                repository,
                TimeSpan.FromSeconds(10),
                16 * 1024);
            return new CommandResult(
                result.ExitCode,
                Encoding.UTF8.GetString(result.StandardOutput),
                Encoding.UTF8.GetString(result.StandardError));
        }

        internal void KillProcesses(IEnumerable<int> processIds)
        {
            foreach (var processId in processIds)
            {
                _ = BoundedProcessRunner.Run(
                    "/bin/kill",
                    ["-KILL", processId.ToString()],
                    repository,
                    TimeSpan.FromSeconds(2),
                    4 * 1024);
            }
        }
    }
}
