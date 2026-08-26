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
        ProducerWorker = WriteExecutable("producer-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            if ! mkdir "$1" 2>/dev/null; then touch "$2"; fi
            sleep 1
            rmdir "$1" 2>/dev/null || true
            """);
        ConcurrentDriver = WriteExecutable("concurrent-driver.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            supervisor="$1"
            worker="$2"
            state="$3"
            active="$4"
            overlap="$5"
            slots="${6:-}"
            env STRATALINT_SUPERVISOR_ROOT="$state" \
              ${slots:+STRATALINT_LEAN_MAX_CONCURRENCY="$slots"} \
              "$supervisor" --role lean-producer --lean-slot -- "$worker" "$active" "$overlap" &
            first=$!
            env STRATALINT_SUPERVISOR_ROOT="$state" \
              ${slots:+STRATALINT_LEAN_MAX_CONCURRENCY="$slots"} \
              "$supervisor" --role lean-producer --lean-slot -- "$worker" "$active" "$overlap" &
            second=$!
            wait "$first"
            wait "$second"
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
            perl -MPOSIX -e '
              my ($pid_path, $parent_path, $release) = @ARGV;
              my $deadline = time() + 20;
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
                while (!-e $release && time() < $deadline) {
                  select undef, undef, undef, 0.02;
                }
                exit 2 unless -e $release;
                exec "sleep", "60";
              }
              open my $parent, ">", $parent_path or die $!;
              print {$parent} "$$\n";
              close $parent or die $!;
              while (!-e $release && time() < $deadline) {
                select undef, undef, undef, 0.02;
              }
              exit 2 unless -e $release;
            ' "$2" "$3" "$4" &
            wait "$!"
            sleep 60
            """);
        DoubleForkWorker = WriteExecutable("double-fork-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            perl -MPOSIX -e '
              my $path = shift;
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
                  exec "sleep", "60";
                }
                open my $out, ">", $path or die $!;
                print {$out} "$second\n";
                close $out or die $!;
                exit 0;
              }
              waitpid($first, 0);
            ' "$1"
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
    internal string DetachedRelease => Path.Combine(Root, "detached.release");
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
            DetachedWorker, DetachedWorkerPid, DetachedPid, DetachedParentPid, DetachedRelease,
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
