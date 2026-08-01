using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void RestartIgnoresImplementingLabelsOwnedByAnotherHost()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var result = RunRestartPolicy(fixture, "foreign-labels", 10_800);
        var output = System.Text.Encoding.UTF8.GetString(result.StandardOutput);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("RESTART_ENGINE\n", output, StringComparison.Ordinal);
        Assert.DoesNotContain("DEFER-RESTART", output, StringComparison.Ordinal);
    }

    [Fact]
    public void RestartDefersForALiveLocalImplementChild()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var result = RunRestartPolicy(fixture, "active-local", 10_800);
        var output = System.Text.Encoding.UTF8.GetString(result.StandardOutput);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "DEFER-RESTART: 1 local implement child process(es) active",
            output,
            StringComparison.Ordinal);
        Assert.DoesNotContain("RESTART_ENGINE", output, StringComparison.Ordinal);
    }

    [Fact]
    public void RestartForcesAfterTheImplementTimeoutBound()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var result = RunRestartPolicy(fixture, "expired-local", 1);
        var output = System.Text.Encoding.UTF8.GetString(result.StandardOutput);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("FORCE-RESTART: defer bound reached", output, StringComparison.Ordinal);
        Assert.Contains("RESTART_ENGINE\n", output, StringComparison.Ordinal);
        Assert.DoesNotContain("DEFER-RESTART", output, StringComparison.Ordinal);
    }

    private static ProcessOutput RunRestartPolicy(
        TemporaryDirectory fixture,
        string scenario,
        int deferBoundSeconds)
    {
        var root = FindRepositoryRoot();
        var runtime = Path.Combine(fixture.Path, "runtime");
        var bin = Path.Combine(fixture.Path, "bin");
        var maintenanceLog = Path.Combine(fixture.Path, "maintenance.log");
        Directory.CreateDirectory(Path.Combine(runtime, "logs"));
        Directory.CreateDirectory(bin);
        var gh = Path.Combine(bin, "gh");
        File.WriteAllText(gh, "#!/usr/bin/env bash\nprintf '3\\n'\n");
        if (!OperatingSystem.IsWindows())
        {
            File.SetUnixFileMode(
                gh,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        var script =
            """
            set -euo pipefail
            source "$1"
            FKST_RUNTIME_ROOT="$2"
            FKST_MAINTENANCE_LOG="$3"
            FKST_CODEX_TIMEOUT_IMPLEMENT="$5"
            CHANGED=1
            PATH="$6:$PATH"
            export FKST_RUNTIME_ROOT FKST_MAINTENANCE_LOG FKST_CODEX_TIMEOUT_IMPLEMENT PATH
            supervisor_log="$FKST_RUNTIME_ROOT/logs/supervisor-1-$$.log"
            : > "$supervisor_log"
            case "$4" in
              foreign-labels) ;;
              active-local)
                printf 'event=dept_child_spawn dept=github-devloop.implement pid=%s exit_code=pending\n' "$$" > "$supervisor_log"
                ;;
              expired-local)
                printf 'event=dept_child_spawn dept=github-devloop.implement pid=%s exit_code=pending\n' "$$" > "$supervisor_log"
                printf '1\n' > "$FKST_RUNTIME_ROOT/hourly-maintenance.restart-defer-since"
                CHANGED=0
                ;;
              *) exit 91 ;;
            esac
            engine_pid() { printf '%s\n' "$$"; }
            cleanup_old_backups() { :; }
            restart_engine() { printf 'RESTART_ENGINE\n'; }
            restart_if_needed
            """;

        return BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                script,
                "restart-policy-test",
                Path.Combine(root, HourlyMaintenanceScriptPath),
                runtime,
                maintenanceLog,
                scenario,
                deferBoundSeconds.ToString(System.Globalization.CultureInfo.InvariantCulture),
                bin,
            ],
            fixture.Path,
            TimeSpan.FromSeconds(30),
            64 * 1024);
    }
}
