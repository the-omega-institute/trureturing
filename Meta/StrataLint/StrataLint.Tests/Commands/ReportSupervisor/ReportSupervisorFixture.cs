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
        DetachedWorker = WriteExecutable("detached-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            perl -MPOSIX -e 'POSIX::setsid(); exec "sleep", "60"' &
            printf '%s\n' "$!" > "$1"
            wait
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
    internal string ScratchRecord => Path.Combine(Root, "scratch.txt");
    internal string ActiveMarker => Path.Combine(Root, "active");
    internal string OverlapMarker => Path.Combine(Root, "overlap");
    internal string GrandchildPid => Path.Combine(Root, "grandchild.pid");
    internal string ExitedGrandchildPid => ScratchRecord;
    internal string DetachedPid => Path.Combine(Root, "detached.pid");
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
            $"STRATALINT_REPORT_METRICS_LOG={MetricsLog}",
            $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
            Supervisor,
            "--role", "lean-producer", "--lean-slot", "--",
            DetachedWorker, DetachedPid,
        }) info.ArgumentList.Add(argument);
        var process = new Process { StartInfo = info };
        Assert.True(process.Start());
        return process;
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
