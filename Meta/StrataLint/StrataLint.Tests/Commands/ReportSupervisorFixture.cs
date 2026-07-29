using System.Diagnostics;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed class ReportSupervisorFixture : IDisposable
{
    private readonly TemporaryDirectory temporary = new();

    internal ReportSupervisorFixture()
    {
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
            metrics="$3"
            state="$4"
            active="$5"
            overlap="$6"
            env STRATALINT_REPORT_METRICS_LOG="$metrics" STRATALINT_SUPERVISOR_ROOT="$state" \
              "$supervisor" --role lean-producer --lean-slot -- "$worker" "$active" "$overlap" &
            first=$!
            env STRATALINT_REPORT_METRICS_LOG="$metrics" STRATALINT_SUPERVISOR_ROOT="$state" \
              "$supervisor" --role lean-producer --lean-slot -- "$worker" "$active" "$overlap" &
            second=$!
            wait "$first"
            wait "$second"
            """);
        LongRunningWorker = WriteExecutable("long-running-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            sleep 60 &
            printf '%s\n' "$!" > "$1"
            wait
            """);
        ExitingWorker = WriteExecutable("exiting-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            sleep 60 &
            printf '%s\n' "$!" > "$1"
            """);
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
            elif [[ "$*" == *"lstart="* ]]; then
              printf 'synthetic-start-%s\n' "$requested_pid"
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
        FileSizeLimitedDriver = WriteExecutable("file-size-limited-driver.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            ulimit -f 1
            exec "$@"
            """);
    }

    internal string Root => temporary.Path;
    internal string RepositoryRoot => FindRepositoryRoot();
    internal string Supervisor => Path.Combine(
        RepositoryRoot, "Meta", "StrataLint", "scripts", "report", "report-supervisor.sh");
    internal string MetricsLog => Path.Combine(Root, "metrics.jsonl");
    internal string DefaultMetricsLog => Path.Combine(Root, ".stratalint-perf", "events.jsonl");
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
    internal string ScratchWriter { get; }
    internal string ProducerWorker { get; }
    internal string ConcurrentDriver { get; }
    internal string LongRunningWorker { get; }
    internal string ExitingWorker { get; }
    internal string DetachedWorker { get; }
    internal string DoubleForkWorker { get; }
    internal string FileSizeLimitedDriver { get; }

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
            $"STRATALINT_REPORT_METRICS_LOG={MetricsLog}",
            $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
        };
        arguments.AddRange(environment);
        arguments.Add(Supervisor);
        arguments.Add("--role");
        arguments.Add(role);
        if (leanSlot) arguments.Add("--lean-slot");
        arguments.Add("--");
        arguments.Add(command);
        arguments.Add(ScratchRecord);
        return BoundedProcessRunner.Run(
            "env", arguments, Root, TimeSpan.FromSeconds(30), 1024 * 1024);
    }

    internal ProcessOutput RunWithDefaultMetrics(string role, string command) =>
        BoundedProcessRunner.Run(
            "env",
            [
                $"PATH={Root}:{HostPath}",
                $"HOME={Root}",
                $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
                Supervisor,
                "--role", role,
                "--", command, ScratchRecord,
            ],
            Root,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

    internal ProcessOutput RunWithFileSizeLimit(string role, string command) =>
        BoundedProcessRunner.Run(
            FileSizeLimitedDriver,
            [
                "env",
                $"PATH={Root}:{HostPath}",
                $"STRATALINT_REPORT_METRICS_LOG={MetricsLog}",
                $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
                Supervisor,
                "--role", role,
                "--", command, ScratchRecord,
            ],
            Root,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

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
            $"STRATALINT_REPORT_METRICS_LOG={MetricsLog}",
            $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
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
            $"STRATALINT_REPORT_METRICS_LOG={MetricsLog}",
            $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
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

    internal IReadOnlyList<JsonElement> ReadMetrics() => File.ReadAllLines(MetricsLog)
        .Select(line => JsonDocument.Parse(line).RootElement.Clone())
        .ToArray();

    internal IReadOnlyList<JsonElement> ReadDefaultMetrics() => File.ReadAllLines(DefaultMetricsLog)
        .Select(line => JsonDocument.Parse(line).RootElement.Clone())
        .ToArray();

    private string WriteExecutable(string name, string contents)
    {
        var path = Path.Combine(Root, name);
        File.WriteAllText(path, contents + "\n", new UTF8Encoding(false));
        var chmod = BoundedProcessRunner.Run(
            "chmod", ["+x", path], Root, TimeSpan.FromSeconds(10), 4096);
        Assert.Equal(0, chmod.ExitCode);
        return path;
    }

    public void Dispose() => temporary.Dispose();

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}

internal sealed class PhysicalTemporaryDirectory : IDisposable
{
    internal PhysicalTemporaryDirectory()
    {
        var root = Directory.Exists("/private/tmp") ? "/private/tmp" : "/tmp";
        Path = System.IO.Path.Combine(
            root,
            "stratalint-report-caller-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(Path);
    }

    internal string Path { get; }

    public void Dispose() => Directory.Delete(Path, recursive: true);
}
