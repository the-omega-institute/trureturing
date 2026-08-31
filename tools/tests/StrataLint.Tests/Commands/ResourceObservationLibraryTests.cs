using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ResourceObservationLibraryTests
{
    private const string LibraryPath = "tools/scripts/lib/resource-observation-lib.sh";
    private const string BootstrapPath = "tools/scripts/lib/resource-observation-bootstrap.sh";

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
        })
        {
            Assert.Contains($"{field}=UNAVAILABLE", output, StringComparison.Ordinal);
        }
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
            "sequence=9 phase=periodic utc=2026-09-01T02:03:04Z utc_epoch_seconds=1788228184",
            output,
            StringComparison.Ordinal);
        Assert.Contains("cgroup_path=/job.slice", output, StringComparison.Ordinal);
        Assert.Contains("memory_current=101 memory_peak=202 memory_max=max", output, StringComparison.Ordinal);
        Assert.Contains("memory_events=low:0,high:1,max:2,oom:3,oom_kill:4", output, StringComparison.Ordinal);
        Assert.Contains("memory_events_oom=3 memory_events_oom_kill=4", output, StringComparison.Ordinal);
        Assert.Contains("process_count=3", output, StringComparison.Ordinal);
        Assert.Contains("pid:99,ppid:1,pgid:99,rss_kb:100,cpu:00:00:01", output, StringComparison.Ordinal);
        Assert.Contains("pid:101,ppid:100,pgid:99,rss_kb:300,cpu:00:00:03", output, StringComparison.Ordinal);
        Assert.DoesNotContain("pid:500", output, StringComparison.Ordinal);
    }

    [Fact]
    public void BaseLibraryCannotBeReplacedByCandidateCode()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var baseRoot = Path.Combine(temporary.Path, "base");
        var workspace = Path.Combine(temporary.Path, "workspace");
        var baseLibrary = Path.Combine(baseRoot, LibraryPath);
        var candidateLibrary = Path.Combine(workspace, "candidate", LibraryPath);
        Directory.CreateDirectory(Path.GetDirectoryName(baseLibrary)!);
        Directory.CreateDirectory(Path.GetDirectoryName(candidateLibrary)!);
        File.WriteAllText(
            baseLibrary,
            "resource_observe_run_periodic() { \"$@\"; }\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            candidateLibrary,
            "resource_observe_run_periodic() { printf 'FALSE_GREEN_REACHED\\n'; return 0; }\n",
            new UTF8Encoding(false));

        var result = Run(
            temporary,
            "source \"$2\"\nunderlying() { printf 'UNDERLYING_REACHED\\n'; return 23; }\nresource_observation_run_with_base_library \"$BASE_ROOT\" underlying\n",
            $"BASE_ROOT={baseRoot}",
            $"GITHUB_WORKSPACE={workspace}");

        Assert.Equal(23, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("UNDERLYING_REACHED", output, StringComparison.Ordinal);
        Assert.DoesNotContain("FALSE_GREEN_REACHED", output, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingLibraryFallsBackAndPreservesEngineeringStatus()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        AssertLoadFailureFallsBack(temporary, "missing", null, "missing");
    }

    [Fact]
    public void UnreadableLibraryFallsBackAndPreservesEngineeringStatus()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        AssertLoadFailureFallsBack(temporary, "unreadable", "return 0\n", "unreadable", readable: false);
    }

    [Fact]
    public void SyntaxInvalidLibraryFallsBackAndPreservesEngineeringStatus()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        AssertLoadFailureFallsBack(temporary, "syntax", "if then\n", "syntax-error");
    }

    [Fact]
    public void NonzeroSourceLibraryFallsBackAndPreservesEngineeringStatus()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        AssertLoadFailureFallsBack(temporary, "source", "return 41\n", "source-nonzero", expectedSourceExit: 41);
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
            "source \"$1\"\nresource_observe_sample() { printf 'SAMPLE phase=%s observer_pid=%s\\n' \"$5\" \"$6\"; return 0; }\nresource_observe_periodically() { return 0; }\nengineering() { kill -TERM \"$$\"; return 23; }\nresource_observe_run_periodic engineering\n");

        Assert.Equal(23, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("RESOURCE_OBSERVATION_SIGNAL status=OBSERVED signal=TERM", output, StringComparison.Ordinal);
        Assert.Contains("SAMPLE phase=signal-TERM", output, StringComparison.Ordinal);
        Assert.Matches("SAMPLE phase=signal-TERM observer_pid=[1-9][0-9]*", output);
    }

    [Fact]
    public void ResourceCriteriaAreMachineEvaluableBeforeExperiment()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();

        var result = Run(temporary, "source \"$1\"\nresource_observation_emit_criteria\n");

        Assert.Equal(0, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("stall_cpu_threshold_percent=5", output, StringComparison.Ordinal);
        Assert.Contains("stall_window_seconds=600", output, StringComparison.Ordinal);
        Assert.Contains(
            "stall_algorithm=100*delta_process_cpu_seconds/delta_utc_epoch_seconds<5_for_every_adjacent_interval_in_contiguous_600_seconds",
            output,
            StringComparison.Ordinal);
        Assert.Contains(
            "stall_delta_predicate=delta_utc_epoch_seconds>0_and_delta_process_cpu_seconds>=0",
            output,
            StringComparison.Ordinal);
        Assert.Contains("observer_exclusion=sampler_pid_and_descendants", output, StringComparison.Ordinal);
        Assert.Contains("oom_algorithm=later_oom_or_oom_kill_greater_than_baseline", output, StringComparison.Ordinal);
        Assert.Contains("disk_algorithm=baseline_positive_then_later_zero_on_same_exact_mount", output, StringComparison.Ordinal);
        Assert.Contains("external_algorithm=run_failure_and_job_failure_and_step_cancelled_and_no_local_classification", output, StringComparison.Ordinal);
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
        Assert.StartsWith("2\t3\t", output, StringComparison.Ordinal);
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
            "source \"$1\"\nresource_observe_periodically() { return 97; }\nresource_observe_run_periodic bash -c 'exit 0'\n");

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "RESOURCE_OBSERVATION_SAMPLER status=UNAVAILABLE exit=97",
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
            "source \"$1\"\nresource_observe_periodically() { return 97; }\nwrapped_command() { bash -c 'exit 23'; bash -c 'exit 0'; }\nset -e\nresource_observe_run_periodic wrapped_command\n");

        Assert.Equal(23, result.ExitCode);
        Assert.Contains(
            "RESOURCE_OBSERVATION_SAMPLER status=UNAVAILABLE exit=97",
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
            Path.Combine(root, BootstrapPath),
        };
        return TestProcessRunner.Run(
            "env",
            arguments,
            temporary.Path,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);
    }

    private static void AssertLoadFailureFallsBack(
        TemporaryDirectory temporary,
        string caseName,
        string? libraryContents,
        string expectedReason,
        bool readable = true,
        int? expectedSourceExit = null)
    {
        var baseRoot = Path.Combine(temporary.Path, caseName);
        var library = Path.Combine(baseRoot, LibraryPath);
        if (libraryContents is not null)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(library)!);
            File.WriteAllText(library, libraryContents, new UTF8Encoding(false));
            if (!readable)
            {
                if (OperatingSystem.IsWindows())
                    throw new PlatformNotSupportedException("resource observation fixtures require Unix permissions");
                File.SetUnixFileMode(library, UnixFileMode.None);
            }
        }

        var result = Run(
            temporary,
            "source \"$2\"\nengineering() { printf 'ENGINEERING_REACHED\\n'; return 23; }\nresource_observation_run_with_base_library \"$BASE_ROOT\" engineering\n",
            $"BASE_ROOT={baseRoot}");

        Assert.Equal(23, result.ExitCode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("ENGINEERING_REACHED", output, StringComparison.Ordinal);
        Assert.Contains(
            $"RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason={expectedReason}",
            output,
            StringComparison.Ordinal);
        if (expectedSourceExit is not null)
            Assert.Contains($"exit={expectedSourceExit}", output, StringComparison.Ordinal);
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
