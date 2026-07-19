using System.Diagnostics;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ReportSupervisorScriptTests
{
    [Fact]
    public void MissingReportConsumptionFailsClosedWithProducerInstruction()
    {
        using var fixture = new ReportSupervisorFixture();
        var consumer = Path.Combine(
            fixture.RepositoryRoot,
            "Meta", "StrataLint", "scripts", "report-consumer.sh");

        var result = BoundedProcessRunner.Run(
            "bash",
            [consumer, "--role", "ingest-consumer", "--report", Path.Combine(fixture.Root, "missing.json"),
             "--", "/usr/bin/true"],
            fixture.Root,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(
            "make lean-report",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void EachRunUsesIndependentScratchAndWritesStructuredMetrics()
    {
        using var fixture = new ReportSupervisorFixture();

        Assert.Equal(0, fixture.Run("scribe-consumer", leanSlot: false, fixture.ScratchWriter).ExitCode);
        Assert.Equal(0, fixture.Run("ingest-consumer", leanSlot: false, fixture.ScratchWriter).ExitCode);

        var scratchPaths = File.ReadAllLines(fixture.ScratchRecord);
        Assert.Equal(2, scratchPaths.Length);
        Assert.NotEqual(scratchPaths[0], scratchPaths[1]);
        Assert.All(scratchPaths, path => Assert.Contains("/scratch", path, StringComparison.Ordinal));
        Assert.All(scratchPaths, path => Assert.False(Directory.Exists(path)));

        var metrics = fixture.ReadMetrics();
        Assert.Equal(2, metrics.Count);
        Assert.Equal("scribe-consumer", metrics[0].GetProperty("role").GetString());
        Assert.Equal("ingest-consumer", metrics[1].GetProperty("role").GetString());
        Assert.All(metrics, metric =>
        {
            Assert.Equal("stratalint-perf-event-v1", metric.GetProperty("schema").GetString());
            Assert.False(string.IsNullOrWhiteSpace(metric.GetProperty("run_id").GetString()));
            Assert.Equal("resource", metric.GetProperty("kind").GetString());
            Assert.Equal(metric.GetProperty("role").GetString(), metric.GetProperty("stage").GetString());
            Assert.Equal("observation", metric.GetProperty("status").GetString());
            Assert.Matches(
                "^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$",
                metric.GetProperty("ts").GetString());
            Assert.True(metric.GetProperty("pid").GetInt32() > 0);
            Assert.True(metric.GetProperty("elapsed_ms").GetInt64() >= 0);
            Assert.Equal(0, metric.GetProperty("rc").GetInt32());
            Assert.True(metric.GetProperty("fd_peak").GetInt32() >= 0);
            Assert.True(metric.GetProperty("rss_peak_kb").GetInt64() >= 0);
            Assert.True(metric.GetProperty("concurrency_count").GetInt32() >= 0);
            Assert.Equal("local", metric.GetProperty("cohort").GetProperty("venue").GetString());
            Assert.False(string.IsNullOrWhiteSpace(
                metric.GetProperty("cohort").GetProperty("cpu_class").GetString()));
            Assert.Equal("report", metric.GetProperty("context").GetProperty("workload_id").GetString());
            Assert.Equal(
                JsonValueKind.Null,
                metric.GetProperty("context").GetProperty("host_concurrency").ValueKind);
            Assert.Equal(
                metric.GetProperty("fd_peak").GetInt32(),
                metric.GetProperty("resources").GetProperty("fd_peak").GetInt32());
        });
    }

    [Fact]
    public void DefaultMetricsUseTheSharedPerformanceResourceLedger()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.RunWithDefaultMetrics(
            "scribe-consumer",
            fixture.ScratchWriter);

        Assert.Equal(0, result.ExitCode);
        var metric = Assert.Single(fixture.ReadDefaultMetrics());
        Assert.Equal("stratalint-perf-event-v1", metric.GetProperty("schema").GetString());
        Assert.Equal("resource", metric.GetProperty("kind").GetString());
        Assert.Equal("scribe-consumer", metric.GetProperty("role").GetString());
    }

    [Fact]
    public void EarlyDependencyFailureRemovesPrivateRunDirectory()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.RunWithEnvironment(
            "scribe-consumer",
            leanSlot: false,
            fixture.ScratchWriter,
            "PATH=/bin:/usr/bin");

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(Directory.GetDirectories(Path.Combine(fixture.StateRoot, "runs")));
    }

    [Fact]
    public void WorkerFailureIsRecordedWithItsExitCode()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.Run("ingest-consumer", leanSlot: false, "/usr/bin/false");

        Assert.Equal(1, result.ExitCode);
        var metric = Assert.Single(fixture.ReadMetrics());
        Assert.Equal("ingest-consumer", metric.GetProperty("role").GetString());
        Assert.Equal(1, metric.GetProperty("rc").GetInt32());
        Assert.Equal("observation", metric.GetProperty("status").GetString());
    }

    [Fact]
    public void OwnerlessSlotIsNeverGuessedStale()
    {
        using var fixture = new ReportSupervisorFixture();
        var ownerlessLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(ownerlessLock);

        var result = fixture.RunWithEnvironment(
            "lean-producer",
            leanSlot: true,
            fixture.ScratchWriter,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(Directory.Exists(ownerlessLock));
    }

    [Fact]
    public void LockOwnedByADeadProcessIsReclaimed()
    {
        using var fixture = new ReportSupervisorFixture();
        var deadLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(deadLock);
        File.WriteAllText(
            Path.Combine(deadLock, "owner"),
            "99999999\n",
            new UTF8Encoding(false));

        var result = fixture.Run("lean-producer", leanSlot: true, fixture.ScratchWriter);

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void LockWhosePidWasReusedIsReclaimed()
    {
        using var fixture = new ReportSupervisorFixture();
        var reusedLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(reusedLock);
        File.WriteAllText(
            Path.Combine(reusedLock, "owner"),
            $"{Environment.ProcessId}|not-the-current-process-start\n",
            new UTF8Encoding(false));

        var result = fixture.Run("lean-producer", leanSlot: true, fixture.ScratchWriter);

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void AbandonedOwnerlessSlotIsReclaimedAfterInitializationGrace()
    {
        using var fixture = new ReportSupervisorFixture();
        var abandonedLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(abandonedLock);
        Directory.SetLastWriteTimeUtc(abandonedLock, DateTime.UtcNow.AddMinutes(-1));

        var result = fixture.Run("lean-producer", leanSlot: true, fixture.ScratchWriter);

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void LiveSlotWaitIsBounded()
    {
        using var fixture = new ReportSupervisorFixture();
        var liveLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(liveLock);
        File.WriteAllText(
            Path.Combine(liveLock, "owner"),
            Environment.ProcessId.ToString(System.Globalization.CultureInfo.InvariantCulture) + "\n",
            new UTF8Encoding(false));

        var result = fixture.RunWithEnvironment(
            "lean-producer",
            leanSlot: true,
            fixture.ScratchWriter,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(
            "timed out",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void MetricsCommitFailureIsNotSilent()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.RunWithEnvironment(
            "scribe-consumer",
            leanSlot: false,
            fixture.ScratchWriter,
            $"STRATALINT_REPORT_METRICS_LOG={fixture.Root}");

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(
            "performance event",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void MetricsShortWriteRollsBackIncompleteEvent()
    {
        using var fixture = new ReportSupervisorFixture();
        var original = Encoding.UTF8.GetBytes(
            "{\"seed\":\"" + new string('x', 380) + "\"}\n");
        File.WriteAllBytes(fixture.MetricsLog, original);

        var result = fixture.RunWithFileSizeLimit(
            "scribe-consumer",
            fixture.ScratchWriter);

        Assert.Equal(2, result.ExitCode);
        Assert.True(File.Exists(fixture.MetricsLog));
        Assert.Equal(original, File.ReadAllBytes(fixture.MetricsLog));
        Assert.Contains(
            "performance event",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void MetricsTimeoutDoesNotRemoveAnotherWritersLock()
    {
        using var fixture = new ReportSupervisorFixture();
        var liveLock = fixture.MetricsLog + ".lock";
        Directory.CreateDirectory(liveLock);
        File.WriteAllText(
            Path.Combine(liveLock, "owner"),
            Environment.ProcessId.ToString(System.Globalization.CultureInfo.InvariantCulture) + "\n",
            new UTF8Encoding(false));

        var result = fixture.RunWithEnvironment(
            "scribe-consumer",
            leanSlot: false,
            fixture.ScratchWriter,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(Directory.Exists(liveLock));
    }

    [Fact]
    public void DefaultLeanSlotSerializesConcurrentProducers()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = BoundedProcessRunner.Run(
            "bash",
            [fixture.ConcurrentDriver, fixture.Supervisor, fixture.ProducerWorker,
             fixture.MetricsLog, fixture.StateRoot, fixture.ActiveMarker, fixture.OverlapMarker],
            fixture.Root,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.False(File.Exists(fixture.OverlapMarker));
        var metrics = fixture.ReadMetrics();
        Assert.Equal(2, metrics.Count);
        Assert.All(metrics, metric =>
        {
            Assert.Equal("lean-producer", metric.GetProperty("role").GetString());
            Assert.Equal(1, metric.GetProperty("concurrency_count").GetInt32());
        });
    }

    [Fact]
    public void TerminationReapsTheWorkerProcessTree()
    {
        using var fixture = new ReportSupervisorFixture();
        using var process = fixture.StartLongRunningProducer();
        Assert.True(SpinWait.SpinUntil(
            () => File.Exists(fixture.GrandchildPid),
            TimeSpan.FromSeconds(10)));
        var grandchild = int.Parse(
            File.ReadAllText(fixture.GrandchildPid).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        var signal = BoundedProcessRunner.Run(
            "/bin/kill",
            ["-TERM", process.Id.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            fixture.Root,
            TimeSpan.FromSeconds(10),
            4096);
        Assert.Equal(0, signal.ExitCode);
        Assert.True(process.WaitForExit(10_000));

        Assert.True(SpinWait.SpinUntil(
            () => !ProcessExists(grandchild),
            TimeSpan.FromSeconds(10)));
        Assert.False(ProcessExists(grandchild));
        var metric = Assert.Single(fixture.ReadMetrics());
        Assert.Equal(143, metric.GetProperty("rc").GetInt32());
    }

    [Fact]
    public void WorkerExitReapsBackgroundDescendants()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.Run(
            "lean-producer",
            leanSlot: true,
            fixture.ExitingWorker);
        Assert.Equal(0, result.ExitCode);
        var grandchild = int.Parse(
            File.ReadAllText(fixture.ExitedGrandchildPid).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        try
        {
            Assert.True(SpinWait.SpinUntil(
                () => !ProcessExists(grandchild),
                TimeSpan.FromSeconds(10)));
        }
        finally
        {
            if (ProcessExists(grandchild))
            {
                _ = BoundedProcessRunner.Run(
                    "/bin/kill",
                    ["-KILL", grandchild.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                    fixture.Root,
                    TimeSpan.FromSeconds(5),
                    4096);
            }
        }
    }

    [Fact]
    public void TerminationReapsADescendantThatCreatesANewSession()
    {
        using var fixture = new ReportSupervisorFixture();
        using var process = fixture.StartDetachedProducer();
        Assert.True(SpinWait.SpinUntil(
            () => File.Exists(fixture.DetachedPid)
                && new FileInfo(fixture.DetachedPid).Length > 0,
            TimeSpan.FromSeconds(10)));
        var detached = int.Parse(
            File.ReadAllText(fixture.DetachedPid).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        var signal = BoundedProcessRunner.Run(
            "/bin/kill",
            ["-TERM", process.Id.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            fixture.Root,
            TimeSpan.FromSeconds(10),
            4096);
        Assert.Equal(0, signal.ExitCode);
        Assert.True(process.WaitForExit(10_000));

        Assert.True(SpinWait.SpinUntil(
            () => !ProcessExists(detached),
            TimeSpan.FromSeconds(10)));
        Assert.False(ProcessExists(detached));
    }

    [Fact]
    public void WorkerExitReapsAFastDoubleForkedSession()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.Run(
            "lean-producer",
            leanSlot: true,
            fixture.DoubleForkWorker);
        Assert.Equal(0, result.ExitCode);
        var detached = int.Parse(
            File.ReadAllText(fixture.DoubleForkPid).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        Assert.True(SpinWait.SpinUntil(
            () => !ProcessExists(detached),
            TimeSpan.FromSeconds(10)));
        Assert.False(ProcessExists(detached));
    }

    private static bool ProcessExists(int pid)
    {
        var result = BoundedProcessRunner.Run(
            "/bin/kill",
            ["-0", pid.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            Directory.GetCurrentDirectory(),
            TimeSpan.FromSeconds(5),
            4096);
        return result.ExitCode == 0;
    }

    private sealed class ReportSupervisorFixture : IDisposable
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
        internal string Supervisor => Path.Combine(RepositoryRoot, "Meta", "StrataLint", "scripts", "report-supervisor.sh");
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
}
