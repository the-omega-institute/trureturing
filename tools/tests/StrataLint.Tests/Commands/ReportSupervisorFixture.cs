using System.Diagnostics;
using System.Text;
using StrataLint.Engine;
using Xunit;

namespace StrataLint.Tests;

internal sealed class ReportSupervisorFixture : IDisposable
{
    private static readonly TimeSpan defaultSafetyTimeout = TestBudgets.ReportSupervisorHangGuard;
    private readonly TemporaryDirectory temporary = new();
    private readonly TimeSpan safetyTimeout;

    internal ReportSupervisorFixture(TimeSpan? safetyTimeout = null)
    {
        this.safetyTimeout = safetyTimeout ?? defaultSafetyTimeout;
        if (this.safetyTimeout <= TestBudgets.ZeroDuration)
        {
            throw new ArgumentOutOfRangeException(
                nameof(safetyTimeout),
                "the report-supervisor test safety timeout must be positive");
        }
        ScratchWriter = WriteExecutable("scratch-writer.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' "$TMPDIR" >> "$1"
            """);
        _ = WriteExecutable("mkdir", """
            #!/usr/bin/env bash
            set -euo pipefail
            event_fifo="${STRATALINT_TEST_SLOT_EVENT_FIFO:-}"
            if [[ -n "$event_fifo" && "$#" == "1" && "$1" == */slot-*.lock ]]; then
              set +e
              /bin/mkdir "$@"
              rc=$?
              set -e
              if (( rc == 0 )); then state=acquired; else state=blocked; fi
              printf '%s:%s\n' "$state" "${1##*/}" > "$event_fifo"
              exit "$rc"
            fi
            exec /bin/mkdir "$@"
            """);
        ProducerWorker = WriteExecutable("producer-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            printf 'acquired\n' > "$1"
            IFS= read -r _ < "$2"
            """);
        ConcurrentDriver = WriteExecutable("concurrent-driver.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            supervisor="$1"
            worker="$2"
            state="$3"
            overlap="$5"
            slots="${6:-}"
            fixture_bin="$(cd "$(dirname "$worker")" && pwd -P)"
            run="$state/concurrency-$$"
            first_acquired="$run/first-acquired.fifo"
            second_acquired="$run/second-acquired.fifo"
            second_acquisition="$run/second-acquisition.fifo"
            first_release="$run/first-release.fifo"
            second_release="$run/second-release.fifo"
            mkdir -p "$run"
            mkfifo "$first_acquired" "$second_acquired" "$second_acquisition" \
              "$first_release" "$second_release"
            first=""
            second=""
            cleanup() {
              [[ -z "$first" ]] || kill "$first" 2>/dev/null || true
              [[ -z "$second" ]] || kill "$second" 2>/dev/null || true
            }
            read_acquisition() {
              while ! IFS= read -r acquisition_event < "$second_acquisition"; do :; done
            }
            trap cleanup EXIT
            env STRATALINT_SUPERVISOR_ROOT="$state" \
              PATH="$fixture_bin:$PATH" \
              ${slots:+STRATALINT_LEAN_MAX_CONCURRENCY="$slots"} \
              "$supervisor" --role lean-producer --lean-slot -- \
              "$worker" "$first_acquired" "$first_release" &
            first=$!
            IFS= read -r _ < "$first_acquired"
            env STRATALINT_SUPERVISOR_ROOT="$state" \
              STRATALINT_TEST_SLOT_EVENT_FIFO="$second_acquisition" \
              PATH="$fixture_bin:$PATH" \
              ${slots:+STRATALINT_LEAN_MAX_CONCURRENCY="$slots"} \
              "$supervisor" --role lean-producer --lean-slot -- \
              "$worker" "$second_acquired" "$second_release" &
            second=$!
            read_acquisition
            first_event="$acquisition_event"
            [[ "$first_event" == "blocked:slot-1.lock" ]]
            if [[ "$slots" == "1" ]]; then
              printf 'release\n' > "$first_release"
              while true; do
                read_acquisition
                second_event="$acquisition_event"
                [[ "$second_event" == "blocked:slot-1.lock" ]] && continue
                [[ "$second_event" == "acquired:slot-1.lock" ]]
                break
              done
              IFS= read -r _ < "$second_acquired"
              printf 'release\n' > "$second_release"
            else
              read_acquisition
              second_event="$acquisition_event"
              [[ "$second_event" == "acquired:slot-2.lock" ]]
              IFS= read -r _ < "$second_acquired"
              kill -0 "$first"
              : > "$overlap"
              printf 'release\n' > "$first_release"
              printf 'release\n' > "$second_release"
            fi
            wait "$first"
            wait "$second"
            trap - EXIT
            """);
        LongRunningWorker = WriteExecutable("long-running-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            release="$PWD/long-running-release.fifo"
            mkfifo "$release"
            { IFS= read -r _ < "$release"; } &
            printf '%s\n' "$!" > "$1"
            wait "$!"
            """);
        ExitingWorker = WriteExecutable("exiting-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            release="$PWD/exiting-worker-release.fifo"
            mkfifo "$release"
            { IFS= read -r _ < "$release"; } &
            printf '%s\n' "$!" > "$1"
            """);
        LsofRaceWorker = WriteExecutable("lsof-race-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            candidate_release="$PWD/lsof-candidate-release.fifo"
            lsof_complete="$PWD/lsof-complete.fifo"
            mkfifo "$candidate_release" "$lsof_complete"
            { IFS= read -r _ < "$candidate_release"; } &
            candidate="$!"
            printf '%s\n' "$candidate" > "$1"
            wait "$candidate"
            : > "$PWD/lsof-candidate-exited"
            IFS= read -r _ < "$lsof_complete"
            printf 'completed\n' > "$1"
            """);
        StepClock = WriteExecutable("step-clock.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            lock="$PWD/step-clock.lock"
            while ! mkdir "$lock" 2>/dev/null; do :; done
            trap 'rmdir "$lock"' EXIT
            read -r current < "$PWD/step-clock.state"
            printf '%s\n' "$((current + 1))" > "$PWD/step-clock.state.tmp.$$"
            mv "$PWD/step-clock.state.tmp.$$" "$PWD/step-clock.state"
            printf '%s\n' "$current"
            """);
        File.WriteAllText(
            Path.Combine(Root, "step-clock.state"),
            "2000000000\n",
            new UTF8Encoding(false));
        _ = WriteExecutable("ps", """
            #!/usr/bin/env bash
            set -euo pipefail
            previous=""
            requested_pid=""
            for argument in "$@"; do
              if [[ "$previous" == "-p" ]]; then requested_pid="$argument"; fi
              previous="$argument"
            done
            if [[ "$*" == *"pid=,ppid=,etime="* ]]; then
              for pid_file in "$PWD/detached.pid" "$PWD/grandchild.pid" "$PWD/scratch.txt"; do
                [[ -s "$pid_file" ]] || continue
                read -r pid < "$pid_file"
                kill -0 "$pid" 2>/dev/null && printf '%s 1 00:00\n' "$pid"
              done
              :
            elif [[ "$*" == *"lstart="* ]]; then
              [[ ! -e "$PWD/ps-owner-exited" ]] || exit 1
              printf 'synthetic-start-%s\n' "$requested_pid"
            elif [[ "$*" == *"command="* ]]; then
              if [[ "${STRATALINT_TEST_PS_FAIL_AFTER_COMMAND:-}" == "1" ]]; then
                : > "$PWD/ps-owner-exited"
              fi
              if [[ "${STRATALINT_TEST_PS_PAUSE_ON_COMMAND:-}" == "1" ]]; then
                : > "$PWD/ps-command-observed"
                while [[ ! -e "$PWD/ps-command-release" ]]; do :; done
              fi
              printf 'synthetic-command-%s\n' "$requested_pid"
            elif [[ "$*" == *"stat="* ]]; then
              printf 'S\n'
            elif [[ "$*" == *"rss="* ]]; then
              printf '0\n'
            else
              exit 1
            fi
            """);
        _ = WriteExecutable("pgrep", """
            #!/usr/bin/env bash
            set -euo pipefail
            [[ "$#" == "2" && "$1" == "-P" && "$2" =~ ^[1-9][0-9]*$ ]] || exit 2
            parent="$2"
            worker=""
            helper=""
            detached=""
            [[ -s "$PWD/detached-worker.pid" ]] && read -r worker < "$PWD/detached-worker.pid"
            [[ -s "$PWD/detached-parent.pid" ]] && read -r helper < "$PWD/detached-parent.pid"
            [[ -s "$PWD/detached.pid" ]] && read -r detached < "$PWD/detached.pid"
            if [[ -n "$worker" && "$parent" == "$worker" \
              && -n "$helper" ]] && kill -0 "$helper" 2>/dev/null; then
              printf '%s\n' "$helper"
            elif [[ -n "$helper" && "$parent" == "$helper" \
              && -n "$detached" ]] && kill -0 "$detached" 2>/dev/null; then
              printf '%s\n' "$detached"
            fi
            for pid_file in "$PWD/grandchild.pid" "$PWD/scratch.txt"; do
              [[ -s "$pid_file" ]] || continue
              read -r pid < "$pid_file"
              if [[ "$pid" =~ ^[1-9][0-9]*$ && "$pid" != "$parent" ]] \
                && kill -0 "$pid" 2>/dev/null; then
                printf '%s\n' "$pid"
              fi
            done
            """);
        DetachedWorker = WriteExecutable("detached-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' "$$" > "$1"
            mkfifo "$4" "$5" "$6"
            perl -MPOSIX -e '
              my ($pid_path, $parent_path, $parent_release, $child_release) = @ARGV;
              my $child = fork();
              die "fork failed" unless defined $child;
              if ($child == 0) {
                POSIX::setsid();
                open my $out, ">", $pid_path or die $!;
                print {$out} "$$\n";
                close $out or die $!;
                close STDOUT;
                close STDERR;
                POSIX::close(9);
                open my $hold, "<", $child_release or die $!;
                <$hold>;
                exit 0;
              }
              open my $parent, ">", $parent_path or die $!;
              print {$parent} "$$\n";
              close $parent or die $!;
              open my $release, "<", $parent_release or die $!;
              <$release>;
            ' "$2" "$3" "$4" "$5" &
            wait "$!"
            IFS= read -r _ < "$6"
            """);
        DoubleForkWorker = WriteExecutable("double-fork-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            release="$PWD/double-fork-release.fifo"
            mkfifo "$release"
            perl -MPOSIX -e '
              my ($path, $release) = @ARGV;
              my $first = fork();
              die "first fork failed" unless defined $first;
              if ($first == 0) {
                POSIX::setsid();
                my $second = fork();
                die "second fork failed" unless defined $second;
                if ($second == 0) {
                  $^F = 9;
                  open STDOUT, ">", "/dev/null" or die $!;
                  open STDERR, ">", "/dev/null" or die $!;
                  open my $hold, "<", $release or die $!;
                  <$hold>;
                  exit 0;
                }
                open my $out, ">", $path or die $!;
                print {$out} "$second\n";
                close $out or die $!;
                exit 0;
              }
              waitpid($first, 0);
            ' "$1" "$release"
            """);
    }

    internal string Root => temporary.Path;
    internal string RepositoryRoot => TestRepositoryLayout.FindRoot();
    internal string Supervisor => Path.Combine(
        RepositoryRoot, "tools", "scripts", "report", "report-supervisor.sh");
    internal string StateRoot => Path.Combine(Root, "state");
    internal string HostPath => Environment.GetEnvironmentVariable("PATH") ?? "/bin:/usr/bin";
    internal string ScratchRecord => Path.Combine(Root, "scratch.txt");
    internal string ActiveMarker => Path.Combine(Root, "active");
    internal string OverlapMarker => Path.Combine(Root, "overlap");
    internal string GrandchildPid => Path.Combine(Root, "grandchild.pid");
    internal string ExitedGrandchildPid => ScratchRecord;
    internal string DetachedPid => Path.Combine(Root, "detached.pid");
    internal string DetachedWorkerPid => Path.Combine(Root, "detached-worker.pid");
    internal string DetachedParentPid => Path.Combine(Root, "detached-parent.pid");
    internal string DetachedParentRelease => Path.Combine(Root, "detached-parent-release.fifo");
    internal string DetachedChildRelease => Path.Combine(Root, "detached-child-release.fifo");
    internal string DetachedWorkerRelease => Path.Combine(Root, "detached-worker-release.fifo");
    internal string DoubleForkPid => ScratchRecord;
    internal string FailingLsofInvocation => Path.Combine(Root, "lsof-invocations.txt");
    internal string ClockEnvironment => $"STRATALINT_SUPERVISOR_CLOCK={StepClock}";
    internal long ClockReads => long.Parse(
        File.ReadAllText(Path.Combine(Root, "step-clock.state")).Trim(),
        System.Globalization.CultureInfo.InvariantCulture) - 2_000_000_000L;
    internal string ScratchWriter { get; }
    internal string ProducerWorker { get; }
    internal string ConcurrentDriver { get; }
    internal string LongRunningWorker { get; }
    internal string ExitingWorker { get; }
    internal string LsofRaceWorker { get; }
    internal string StepClock { get; }
    internal string DetachedWorker { get; }
    internal string DoubleForkWorker { get; }

    internal TimeSpan SafetyTimeout => safetyTimeout;

    internal ProcessOutput Run(string role, bool leanSlot, string command)
        => RunWithEnvironment(role, leanSlot, command);

    internal ProcessOutput RunWithEnvironment(
        string role,
        bool leanSlot,
        string command,
        params string[] environment)
    {
        var arguments = new List<string>
        {
            $"PATH={Root}:{HostPath}",
            $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=86400",
        };
        arguments.AddRange(environment);
        arguments.Add(Supervisor);
        arguments.Add("--role");
        arguments.Add(role);
        if (leanSlot) arguments.Add("--lean-slot");
        arguments.Add("--");
        arguments.Add(command);
        arguments.Add(ScratchRecord);
        return TestProcessRunner.Run(
            "env", arguments, Root, safetyTimeout, 1024 * 1024);
    }

    internal ProcessOutput RunExternalProcess(
        string fileName,
        IEnumerable<string> arguments,
        string? workingDirectory = null,
        int maximumOutputBytes = 1024 * 1024) =>
        TestProcessRunner.Run(
            fileName,
            arguments,
            workingDirectory ?? Root,
            safetyTimeout,
            maximumOutputBytes);

    internal void InstallLsofRaceHarness()
    {
        _ = WriteExecutable("lsof", """
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' "$*" >> "$PWD/lsof-invocations.txt"
            if [[ "$*" == *"0-999999"* ]]; then exit 1; fi
            printf 'release\n' > "$PWD/lsof-candidate-release.fifo"
            while [[ ! -e "$PWD/lsof-candidate-exited" ]]; do :; done
            printf 'complete\n' > "$PWD/lsof-complete.fifo"
            exit 1
            """);
    }

    internal Process StartSentinelBlockedProcess()
    {
        var release = Path.Combine(Root, "owner-release.fifo");
        var ready = Path.Combine(Root, "owner-ready");
        var blocker = WriteExecutable("owner-blocker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            : > "$2"
            IFS= read -r _ < "$1"
            """);
        var mkfifo = RunExternalProcess("mkfifo", [release], maximumOutputBytes: 4096);
        Assert.Equal(0, mkfifo.ExitCode);
        var process = new Process
        {
            StartInfo = new ProcessStartInfo
            {
                FileName = blocker,
                WorkingDirectory = Root,
                UseShellExecute = false,
            },
        };
        process.StartInfo.ArgumentList.Add(release);
        process.StartInfo.ArgumentList.Add(ready);
        Assert.True(process.Start());
        WaitUntil(() => File.Exists(ready), "sentinel-blocked owner did not become ready");
        return process;
    }

    internal void WaitUntil(Func<bool> condition, string failureMessage)
    {
        if (!SpinWait.SpinUntil(condition, safetyTimeout))
        {
            throw new SkipException(
                $"infrastructure-hang-guard expired: {failureMessage} ({safetyTimeout})");
        }
    }

    internal void WaitForExit(Process process, string failureMessage) =>
        WaitUntil(() => process.HasExited, failureMessage);

    internal Process StartLongRunningProducer()
    {
        var info = new ProcessStartInfo
        {
            FileName = "env",
            WorkingDirectory = Root,
            UseShellExecute = false,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
        };
        foreach (var argument in new[]
        {
            $"PATH={Root}:{HostPath}",
            $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=86400",
            Supervisor,
            "--role", "lean-producer", "--lean-slot", "--",
            LongRunningWorker, GrandchildPid,
        }) info.ArgumentList.Add(argument);
        var process = new Process { StartInfo = info };
        Assert.True(process.Start());
        return process;
    }

    internal Process StartDetachedProducer()
    {
        var info = new ProcessStartInfo
        {
            FileName = "env",
            WorkingDirectory = Root,
            UseShellExecute = false,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
        };
        foreach (var argument in new[]
        {
            $"PATH={Root}:{HostPath}",
            $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=86400",
            Supervisor,
            "--role", "lean-producer", "--lean-slot", "--",
            DetachedWorker, DetachedWorkerPid, DetachedPid, DetachedParentPid,
            DetachedParentRelease, DetachedChildRelease, DetachedWorkerRelease,
        }) info.ArgumentList.Add(argument);
        var process = new Process { StartInfo = info };
        Assert.True(process.Start());
        return process;
    }

    internal bool HasRecordedProcessCandidate(int pid)
    {
        var runs = Path.Combine(StateRoot, "runs");
        if (!Directory.Exists(runs)) return false;
        var prefix = pid.ToString(System.Globalization.CultureInfo.InvariantCulture) + "|";
        return Directory.EnumerateFiles(
                runs,
                "process-candidates",
                SearchOption.AllDirectories)
            .Any(path => File.ReadLines(path)
                .Any(line => line.StartsWith(prefix, StringComparison.Ordinal)));
    }

    private string WriteExecutable(string name, string contents)
    {
        var path = Path.Combine(Root, name);
        File.WriteAllText(path, contents + "\n", new UTF8Encoding(false));
        if (!OperatingSystem.IsWindows())
        {
            File.SetUnixFileMode(
                path,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        return path;
    }

    public void Dispose() => temporary.Dispose();
}
