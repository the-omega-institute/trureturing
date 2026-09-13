using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ResourceObservationLibraryTests
{
    private const string LibraryPath = "tools/scripts/lib/resource-observation-lib.sh";

    [Theory]
    [InlineData("D5/Probe.lean", "D5/Probe.lean", 0)]
    [InlineData("D5/Space Name.lean", "D5/Space\\ Name.lean", 23)]
    public void LeanInputDiagnosticsPreserveSourceArgumentsAndCommandExit(
        string source, string escapedSource, int commandExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var proc = InstallLeanInputFixture(temporary, source);

        var result = Run(temporary, LeanInputSampleScript,
            $"RESOURCE_OBSERVATION_PROC_ROOT={proc}", $"COMMAND_EXIT={commandExit}");

        Assert.Equal(commandExit, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains($"RESOURCE_LEAN_INPUT sequence=0 phase=baseline pid=100 status=OBSERVED source={escapedSource}\n",
            output, StringComparison.Ordinal);
        Assert.Contains($"RESOURCE_LEAN_INPUT sequence=0 phase=final pid=100 status=OBSERVED source={escapedSource}\n",
            output, StringComparison.Ordinal);
        Assert.DoesNotContain("private-value", output, StringComparison.Ordinal);
        Assert.DoesNotContain("Unrelated.lean", output, StringComparison.Ordinal);
        Assert.DoesNotContain("Option.lean", output, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing-process", "executable-unavailable", 0)]
    [InlineData("missing-cmdline", "cmdline-unavailable", 23)]
    [InlineData("unreadable-cmdline", "cmdline-unavailable", 0)]
    [InlineData("no-proc", "proc-unavailable", 23)]
    public void UnavailableLeanInputDiagnosticsDoNotChangeCommandExit(
        string fault, string reason, int commandExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var proc = InstallLeanInputFixture(temporary, "D5/Probe.lean");
        var cmdline = Path.Combine(proc, "100/cmdline");
        if (fault == "missing-process") Directory.Delete(Path.Combine(proc, "100"), true);
        if (fault == "missing-cmdline") File.Delete(cmdline);
        if (fault == "unreadable-cmdline") File.SetUnixFileMode(cmdline, UnixFileMode.None);
        if (fault == "no-proc") proc = Path.Combine(temporary.Path, "absent-proc");
        try
        {
            var result = Run(temporary, LeanInputSampleScript,
                $"RESOURCE_OBSERVATION_PROC_ROOT={proc}", $"COMMAND_EXIT={commandExit}");
            Assert.Equal(commandExit, result.ExitCode);
            var output = Encoding.UTF8.GetString(result.StandardOutput);
            Assert.Contains("RESOURCE_LEAN_INPUT sequence=0 phase=baseline", output, StringComparison.Ordinal);
            Assert.Contains($"status=UNAVAILABLE reason={reason}", output, StringComparison.Ordinal);
            Assert.Contains($"phase=final stall_cpu_threshold_percent=5 stall_window_seconds=600 command_exit_status={commandExit}",
                output, StringComparison.Ordinal);
            Assert.DoesNotContain("status=OBSERVED source=", output, StringComparison.Ordinal);
        }
        finally
        {
            if (fault == "unreadable-cmdline") File.SetUnixFileMode(cmdline, UnixFileMode.UserRead | UnixFileMode.UserWrite);
        }
    }

    private const string LeanInputSampleScript = """
        set -euo pipefail
        source "$1"
        resource_observation_process_values() {
          printf '2\t5\tpid:100,ppid:99,pgid:99,rss_kb:200,cpu:00:00:02;pid:101,ppid:99,pgid:99,rss_kb:300,cpu:00:00:03\n'
        }
        resource_observe_periodically() { return 0; }
        observed_command() { return "$COMMAND_EXIT"; }
        resource_observe_run_periodic observed_command
        """;

    private static string InstallLeanInputFixture(TemporaryDirectory temporary, string source)
    {
        var proc = Path.Combine(temporary.Path, "proc");
        foreach (var pid in new[] { "100", "101", "500" }) Directory.CreateDirectory(Path.Combine(proc, pid));
        File.CreateSymbolicLink(Path.Combine(proc, "100/exe"), "/fixture/toolchain/bin/lean");
        File.CreateSymbolicLink(Path.Combine(proc, "101/exe"), "/fixture/toolchain/bin/worker");
        File.CreateSymbolicLink(Path.Combine(proc, "500/exe"), "/fixture/toolchain/bin/lean");
        File.WriteAllText(Path.Combine(proc, "100/cmdline"),
            $"/fixture/toolchain/bin/lean\0--run\0{source}\0--private=private-value\0--output=Option.lean\0", new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(proc, "101/cmdline"), "lean\0Unrelated.lean\0", new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(proc, "500/cmdline"), "lean\0Unrelated.lean\0", new UTF8Encoding(false));
        return proc;
    }

    [Fact]
    public void UnreadableSourcesEmitUnavailableForEveryField()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var missing = Path.Combine(temporary.Path, "missing");

        var result = Run(
            temporary,
            "source \"$1\"\nresource_observe_sample 7 424242 \"\" \"\"\n",
            $"RESOURCE_OBSERVATION_PROC_ROOT={missing}",
            $"RESOURCE_OBSERVATION_CGROUP_ROOT={missing}",
            $"RESOURCE_OBSERVATION_DATE_COMMAND={missing}",
            $"RESOURCE_OBSERVATION_FINDMNT_COMMAND={missing}",
            $"RESOURCE_OBSERVATION_DF_COMMAND={missing}",
            $"RESOURCE_OBSERVATION_PS_COMMAND={missing}");

        Assert.Equal(1, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("sequence=7", output, StringComparison.Ordinal);
        Assert.Contains(
            "RESOURCE_OBSERVATION_SAMPLE status=UNAVAILABLE sequence=7",
            output,
            StringComparison.Ordinal);
        foreach (var field in new[]
        {
            "utc",
            "cgroup_path",
            "memory_current",
            "memory_peak",
            "memory_max",
            "memory_events",
            "memory_events_oom",
            "memory_events_oom_kill",
            "workspace_mount",
            "workspace_available_blocks_1k",
            "workspace_available_inodes",
            "runner_temp_mount",
            "runner_temp_available_blocks_1k",
            "runner_temp_available_inodes",
            "tmp_mount",
            "tmp_available_blocks_1k",
            "tmp_available_inodes",
            "process_count",
            "process_tree",
            "command_exit_status",
            "termination_signal",
        })
        {
            Assert.Contains($"{field}=UNAVAILABLE", output, StringComparison.Ordinal);
        }
        Assert.Contains("stall_cpu_threshold_percent=5", output, StringComparison.Ordinal);
        Assert.Contains("stall_window_seconds=600", output, StringComparison.Ordinal);
    }

    [Fact]
    public void DistinctMountsReportTheirOwnBlockAndInodeReadings()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var bin = Path.Combine(temporary.Path, "bin");
        Directory.CreateDirectory(bin);
        var findmnt = WriteExecutable(
            bin,
            "findmnt",
            """
            #!/usr/bin/env bash
            target=""
            while [[ $# -gt 0 ]]; do
              if [[ "$1" == "-T" ]]; then target="$2"; shift 2; else shift; fi
            done
            case "$target" in
              /fixture/workspace) printf '/mnt/workspace\n' ;;
              /fixture/runner-temp) printf '/mnt/runner-temp\n' ;;
              /tmp) printf '/mnt/tmp\n' ;;
              *) exit 1 ;;
            esac
            """);
        var df = WriteExecutable(
            bin,
            "df",
            """
            #!/usr/bin/env bash
            mode="$1"
            mount="$2"
            if [[ "$mode" == "-Pk" ]]; then
              printf 'Filesystem 1024-blocks Used Available Capacity Mounted on\n'
              case "$mount" in
                /mnt/workspace) printf 'fixture 1000 1 111 1%% /mnt/workspace\n' ;;
                /mnt/runner-temp) printf 'fixture 1000 1 222 1%% /mnt/runner-temp\n' ;;
                /mnt/tmp) printf 'fixture 1000 1 333 1%% /mnt/tmp\n' ;;
                *) exit 1 ;;
              esac
            elif [[ "$mode" == "-Pi" ]]; then
              printf 'Filesystem Inodes IUsed IFree IUse%% Mounted on\n'
              case "$mount" in
                /mnt/workspace) printf 'fixture 1000 1 444 1%% /mnt/workspace\n' ;;
                /mnt/runner-temp) printf 'fixture 1000 1 555 1%% /mnt/runner-temp\n' ;;
                /mnt/tmp) printf 'fixture 1000 1 666 1%% /mnt/tmp\n' ;;
                *) exit 1 ;;
              esac
            else
              exit 1
            fi
            """);

        var result = Run(
            temporary,
            "source \"$1\"\nresource_observe_sample 2 123 \"$WORKSPACE_FIXTURE\" \"$RUNNER_TEMP_FIXTURE\"\n",
            "WORKSPACE_FIXTURE=/fixture/workspace",
            "RUNNER_TEMP_FIXTURE=/fixture/runner-temp",
            $"RESOURCE_OBSERVATION_PROC_ROOT={Path.Combine(temporary.Path, "missing")}",
            $"RESOURCE_OBSERVATION_FINDMNT_COMMAND={findmnt}",
            $"RESOURCE_OBSERVATION_DF_COMMAND={df}",
            $"RESOURCE_OBSERVATION_PS_COMMAND={Path.Combine(temporary.Path, "missing-ps")}");

        Assert.Equal(1, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("workspace_mount=/mnt/workspace workspace_available_blocks_1k=111 workspace_available_inodes=444", output, StringComparison.Ordinal);
        Assert.Contains("runner_temp_mount=/mnt/runner-temp runner_temp_available_blocks_1k=222 runner_temp_available_inodes=555", output, StringComparison.Ordinal);
        Assert.Contains("tmp_mount=/mnt/tmp tmp_available_blocks_1k=333 tmp_available_inodes=666", output, StringComparison.Ordinal);
    }

    [Fact]
    public void CgroupAndDescendantProcessTreeFieldsAreReadable()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var proc = Path.Combine(temporary.Path, "proc");
        var cgroup = Path.Combine(temporary.Path, "cgroup");
        Directory.CreateDirectory(Path.Combine(proc, "99"));
        Directory.CreateDirectory(Path.Combine(cgroup, "job.slice"));
        File.WriteAllText(Path.Combine(proc, "99", "cgroup"), "0::/job.slice\n", new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(cgroup, "job.slice", "memory.current"), "101\n", new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(cgroup, "job.slice", "memory.peak"), "202\n", new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(cgroup, "job.slice", "memory.max"), "max\n", new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(cgroup, "job.slice", "memory.events"),
            "low 0\nhigh 1\nmax 2\noom 3\noom_kill 4\n",
            new UTF8Encoding(false));
        var bin = Path.Combine(temporary.Path, "bin");
        Directory.CreateDirectory(bin);
        var date = WriteExecutable(
            bin,
            "date",
            "#!/usr/bin/env bash\nif [[ \"$*\" == *'+%s'* ]]; then printf '1788228184\\n'; else printf '2026-09-01T02:03:04Z\\n'; fi\n");
        var ps = WriteExecutable(
            bin,
            "ps",
            """
            #!/usr/bin/env bash
            printf '99 1 99 100 00:00:01\n'
            printf '100 99 99 200 00:00:02\n'
            printf '101 100 99 300 00:00:03\n'
            printf '500 1 500 400 00:00:04\n'
            """);

        var result = Run(
            temporary,
            "source \"$1\"\nresource_observe_sample 9 99 \"\" \"\"\n",
            $"RESOURCE_OBSERVATION_PROC_ROOT={proc}",
            $"RESOURCE_OBSERVATION_CGROUP_ROOT={cgroup}",
            $"RESOURCE_OBSERVATION_DATE_COMMAND={date}",
            $"RESOURCE_OBSERVATION_FINDMNT_COMMAND={Path.Combine(temporary.Path, "missing-findmnt")}",
            $"RESOURCE_OBSERVATION_PS_COMMAND={ps}");

        Assert.Equal(1, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains(
            "sequence=9 phase=periodic stall_cpu_threshold_percent=5 stall_window_seconds=600 command_exit_status=UNAVAILABLE termination_signal=UNAVAILABLE utc=2026-09-01T02:03:04Z utc_epoch_seconds=1788228184",
            output,
            StringComparison.Ordinal);
        Assert.Contains("cgroup_path=/job.slice", output, StringComparison.Ordinal);
        Assert.Contains("memory_current=101 memory_peak=202 memory_max=max", output, StringComparison.Ordinal);
        Assert.Contains("memory_events=low:0,high:1,max:2,oom:3,oom_kill:4", output, StringComparison.Ordinal);
        Assert.Contains("memory_events_oom=3 memory_events_oom_kill=4", output, StringComparison.Ordinal);
        Assert.Contains("process_count=2", output, StringComparison.Ordinal);
        Assert.Contains("process_cpu_seconds=5", output, StringComparison.Ordinal);
        Assert.Contains("pid:100,ppid:99,pgid:99,rss_kb:200,cpu:00:00:02", output, StringComparison.Ordinal);
        Assert.Contains("pid:101,ppid:100,pgid:99,rss_kb:300,cpu:00:00:03", output, StringComparison.Ordinal);
        Assert.DoesNotContain("pid:500", output, StringComparison.Ordinal);
    }

    [Fact]
    public void RealSampleFailuresEmitTypedUnavailable()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(
            temporary,
            "source \"$1\"\nresource_observe_sample() { return 19; }\nsleep() { return 1; }\nresource_observe_periodically 123 \"\" \"\" 1\n");

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "RESOURCE_OBSERVATION_SAMPLER status=UNAVAILABLE reason=sample-failures failed_samples=1",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void SynchronousBaselineSampleRunsBeforeEngineeringCommand()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(
            temporary,
            "source \"$1\"\nresource_observe_sample() { printf 'SAMPLE phase=%s\\n' \"$5\"; return 0; }\nresource_observe_periodically() { return 0; }\nengineering() { printf 'ENGINEERING\\n'; return 0; }\nresource_observe_run_periodic engineering\n");

        Assert.Equal(0, result.ExitCode);
        var lines = Encoding.UTF8.GetString(result.StandardOutput)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.Contains("SAMPLE phase=baseline", lines);
        Assert.True(
            Array.IndexOf(lines, "SAMPLE phase=baseline") < Array.IndexOf(lines, "ENGINEERING"),
            string.Join(Environment.NewLine, lines));
    }

    [Fact]
    public void SynchronousFinalSampleRunsAfterEngineeringCommand()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(
            temporary,
            "source \"$1\"\nresource_observe_sample() { printf 'SAMPLE phase=%s\\n' \"$5\"; return 0; }\nresource_observe_periodically() { return 0; }\nengineering() { printf 'ENGINEERING\\n'; return 0; }\nresource_observe_run_periodic engineering\n");

        Assert.Equal(0, result.ExitCode);
        var lines = Encoding.UTF8.GetString(result.StandardOutput)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.Contains("SAMPLE phase=final", lines);
        Assert.True(
            Array.IndexOf(lines, "SAMPLE phase=final") > Array.IndexOf(lines, "ENGINEERING"),
            string.Join(Environment.NewLine, lines));
    }

    [Fact]
    public void SignalPathEmitsTypedReceiptAndPreservesEngineeringStatus()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(
            temporary,
            """
            source "$1"
            barrier_marker="$PWD/wait-barrier-complete"
            mkfifo sampler-ready sampler-block
            exec 4<>sampler-ready
            exec 3<>sampler-block
            resource_observe_sample() {
              if [[ "$5" == "final" && ! -f "$barrier_marker" ]]; then
                builtin kill -KILL "$sampler_pid" 2>/dev/null || true
                builtin wait "$sampler_pid" 2>/dev/null || true
                return 0
              fi
              printf 'SAMPLE phase=%s observer_pid=%s exit=%s signal=%s\n' "$5" "$6" "$7" "$8"
            }
            resource_observe_periodically() {
              trap '' TERM
              printf 'ready\n' >&4
              read -r _ <&3
            }
            wait_attempt=0
            wait() {
              local wait_status=0
              wait_attempt=$((wait_attempt + 1))
              if [[ "$wait_attempt" -eq 1 ]]; then
                builtin kill -TERM "$$"
                return 143
              fi
              builtin kill -KILL "$sampler_pid" 2>/dev/null || true
              builtin wait "$@"
              wait_status=$?
              : > "$barrier_marker"
              return "$wait_status"
            }
            engineering() { read -r _ <&4; return 23; }
            resource_observe_run_periodic engineering
            """);

        Assert.Equal(23, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("RESOURCE_OBSERVATION_SIGNAL status=OBSERVED signal=TERM", output, StringComparison.Ordinal);
        Assert.Contains("SAMPLE phase=signal-TERM", output, StringComparison.Ordinal);
        Assert.Matches("SAMPLE phase=signal-TERM observer_pid=[1-9][0-9]*", output);
        Assert.Contains("SAMPLE phase=final observer_pid= exit=23 signal=TERM", output, StringComparison.Ordinal);
        Assert.DoesNotContain("RESOURCE_OBSERVATION_SAMPLER", output, StringComparison.Ordinal);
    }

    [Fact]
    public void ResourceCriteriaAreMachineEvaluableBeforeExperiment()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(temporary, "source \"$1\"\nresource_observation_emit_criteria\n");

        Assert.Equal(0, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("RESOURCE_OBSERVATION_CRITERIA version=2", output, StringComparison.Ordinal);
        Assert.Contains("stall_cpu_threshold_percent=5", output, StringComparison.Ordinal);
        Assert.Contains("stall_window_seconds=600", output, StringComparison.Ordinal);
        Assert.Contains(
            "stall_algorithm=100*delta_process_cpu_seconds/delta_utc_epoch_seconds<5_for_every_adjacent_interval_in_contiguous_600_seconds",
            output,
            StringComparison.Ordinal);
        Assert.Contains("stall_sample_predicate=all_stall_fields_available_and_process_count>0", output, StringComparison.Ordinal);
        Assert.Contains(
            "stall_delta_predicate=delta_utc_epoch_seconds>0_and_delta_process_cpu_seconds>=0",
            output,
            StringComparison.Ordinal);
        Assert.Contains("process_count_scope=descendants_excluding_wrapper_and_sampler", output, StringComparison.Ordinal);
        Assert.Contains("stall_output_activity=not_required", output, StringComparison.Ordinal);
        Assert.Contains("oom_algorithm=later_oom_or_oom_kill_greater_than_baseline", output, StringComparison.Ordinal);
        Assert.Contains("disk_algorithm=baseline_positive_then_later_zero_on_same_exact_mount_without_errno_or_quota_claim", output, StringComparison.Ordinal);
        Assert.Contains("external_algorithm=command_exit_status_nonzero_and_termination_signal_observed_and_no_local_classification", output, StringComparison.Ordinal);
    }

    [Fact]
    public void SampleCarriesCriterionParametersAndTerminationFields()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(
            temporary,
            "source \"$1\"\nresource_observe_sample 4 99 \"\" \"\" final \"\" 143 TERM\n",
            $"RESOURCE_OBSERVATION_PROC_ROOT={Path.Combine(temporary.Path, "missing-proc")}",
            $"RESOURCE_OBSERVATION_CGROUP_ROOT={Path.Combine(temporary.Path, "missing-cgroup")}",
            $"RESOURCE_OBSERVATION_DATE_COMMAND={Path.Combine(temporary.Path, "missing-date")}",
            $"RESOURCE_OBSERVATION_FINDMNT_COMMAND={Path.Combine(temporary.Path, "missing-findmnt")}",
            $"RESOURCE_OBSERVATION_DF_COMMAND={Path.Combine(temporary.Path, "missing-df")}",
            $"RESOURCE_OBSERVATION_PS_COMMAND={Path.Combine(temporary.Path, "missing-ps")}");

        Assert.Equal(1, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("stall_cpu_threshold_percent=5 stall_window_seconds=600", output, StringComparison.Ordinal);
        Assert.Contains("command_exit_status=143 termination_signal=TERM", output, StringComparison.Ordinal);
    }

    [Fact]
    public void ObserverProcessSubtreeIsExcludedFromProcessTotals()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var ps = WriteExecutable(
            temporary.Path,
            "ps",
            """
            #!/usr/bin/env bash
            printf '99 1 99 100 00:00:01\n'
            printf '100 99 99 200 00:00:02\n'
            printf '200 99 99 300 00:00:04\n'
            printf '201 200 99 400 00:00:08\n'
            """);

        var result = Run(
            temporary,
            "source \"$1\"\nresource_observation_process_values 99 200\n",
            $"RESOURCE_OBSERVATION_PS_COMMAND={ps}");

        Assert.Equal(0, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.StartsWith("1\t2\t", output, StringComparison.Ordinal);
        Assert.Contains("pid:100", output, StringComparison.Ordinal);
        Assert.DoesNotContain("pid:200", output, StringComparison.Ordinal);
        Assert.DoesNotContain("pid:201", output, StringComparison.Ordinal);
    }

    [Fact]
    public void SamplerFailureDoesNotChangeSuccessfulCommandExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(
            temporary,
            """
            source "$1"
            resource_observe_sample() { return 0; }
            sampler_fifo="$PWD/sampler-exited"
            mkfifo "$sampler_fifo"
            resource_observe_periodically() { exec 9>"$sampler_fifo"; bash -c 'exit 97'; }
            printf() {
              if [[ "$1" == '%s\n' && "${2:-}" == "97" ]]; then
                builtin printf '9'
                return 0
              fi
              builtin printf "$@"
            }
            observed_command() {
              # The shim owns write fd 9; EOF proves its truncated publication attempt is complete.
              read -r _ <"$sampler_fifo" || [[ "$?" -eq 1 ]]
              bash -c 'exit 0'
            }
            resource_observe_run_periodic observed_command
            """);

        Assert.Equal(0, result.ExitCode);
        Assert.DoesNotContain(
            "RESOURCE_OBSERVATION_SAMPLER",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void SamplerFailureDoesNotChangeFailingCommandExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(
            temporary,
            """
            source "$1"
            resource_observe_sample() { return 0; }
            sampler_fifo="$PWD/sampler-exited"
            mkfifo "$sampler_fifo"
            resource_observe_periodically() { exec 9>"$sampler_fifo"; bash -c 'exit 97'; }
            wrapped_command() {
              # The shim owns write fd 9; EOF proves it exited after atomically recording the status.
              read -r _ <"$sampler_fifo" || [[ "$?" -eq 1 ]]
              bash -c 'exit 23'
              bash -c 'exit 0'
            }
            set -e
            resource_observe_run_periodic wrapped_command
            """);

        Assert.Equal(23, result.ExitCode);
        Assert.Contains(
            "RESOURCE_OBSERVATION_SAMPLER status=UNAVAILABLE exit=97",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void PartialBaselineDoesNotPreventPeriodicSampler()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(
            temporary,
            """
            source "$1"
            resource_observe_sample() { return 19; }
            sampler_fifo="$PWD/sampler-exited"
            mkfifo "$sampler_fifo"
            resource_observe_periodically() { exec 9>"$sampler_fifo"; bash -c 'exit 97'; }
            observed_command() {
              # The shim owns write fd 9; EOF proves it exited after atomically recording the status.
              read -r _ <"$sampler_fifo" || [[ "$?" -eq 1 ]]
              bash -c 'exit 0'
            }
            resource_observe_run_periodic observed_command
            """);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "RESOURCE_OBSERVATION_SAMPLER status=UNAVAILABLE exit=97",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void SamplerKilledByWrapperDoesNotEmitUnavailable()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(
            temporary,
            """
            source "$1"
            resource_observe_sample() { return 0; }
            mkfifo sampler-block
            exec 3<>sampler-block
            resource_observe_periodically() { read -r _ <&3; }
            observed_command() {
              printf 'ran\n' > observed-command-ran
              return 23
            }
            set -e
            resource_observe_run_periodic observed_command
            """,
            $"RUNNER_TEMP={Path.Combine(temporary.Path, "missing-runner-temp")}");

        Assert.Equal(23, result.ExitCode);
        Assert.True(File.Exists(Path.Combine(temporary.Path, "observed-command-ran")));
        Assert.DoesNotContain(
            "RESOURCE_OBSERVATION_SAMPLER",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void SamplerThatExitedOnItsOwnReportsItsExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(
            temporary,
            """
            source "$1"
            resource_observe_sample() { return 0; }
            publish_ready="$PWD/publish-ready"
            publish_release="$PWD/publish-release"
            mkfifo "$publish_ready" "$publish_release"
            exec 7<>"$publish_ready"
            exec 8<>"$publish_release"
            resource_observe_periodically() { return 5; }
            mv() {
              printf 'ready\n' >&7
              read -r _ <&8
              command mv "$@"
            }
            kill() {
              builtin kill "$@"
              printf 'release\n' >&8
            }
            observed_command() {
              read -r _ <&7
            }
            resource_observe_run_periodic observed_command
            """);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "RESOURCE_OBSERVATION_SAMPLER status=UNAVAILABLE exit=5",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    private static ProcessOutput Run(
        TemporaryDirectory temporary,
        string script,
        params string[] environment)
    {
        var root = TestRepositoryLayout.FindRoot();
        var arguments = new List<string>(environment)
        {
            "bash",
            "-c",
            script,
            "resource-observation-test",
            Path.Combine(root, LibraryPath),
        };
        return TestProcessRunner.Run(
            "env",
            arguments,
            temporary.Path,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);
    }

    private static string WriteExecutable(string directory, string name, string contents)
    {
        if (OperatingSystem.IsWindows())
            throw new PlatformNotSupportedException("resource observation fixtures require Unix executables");

        var path = Path.Combine(directory, name);
        File.WriteAllText(path, contents + "\n", new UTF8Encoding(false));
        File.SetUnixFileMode(
            path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        return path;
    }
}
