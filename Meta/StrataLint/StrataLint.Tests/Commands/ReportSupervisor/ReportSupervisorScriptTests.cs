using System.Diagnostics;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReportSupervisorScriptTests
{
    [Fact]
    public void MissingReportConsumptionFailsClosedWithProducerInstruction()
    {
        using var fixture = new ReportSupervisorFixture();
        var consumer = Path.Combine(
            fixture.RepositoryRoot,
            "Meta", "StrataLint", "scripts", "report", "report-consumer.sh");

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

        Assert.Equal(0, fixture.RunWithEnvironment(
            "scribe-consumer", leanSlot: false, fixture.ScratchWriter, "CI=false").ExitCode);
        Assert.Equal(0, fixture.RunWithEnvironment(
            "ingest-consumer", leanSlot: false, fixture.ScratchWriter, "CI=false").ExitCode);

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
    public void MetricsWriterUsesRepositoryRootInsteadOfTheCallerWorkingDirectory()
    {
        using var fixture = new ReportSupervisorFixture();
        using var caller = new PhysicalTemporaryDirectory();
        var metrics = Path.Combine(caller.Path, "metrics.jsonl");
        var state = Path.Combine(caller.Path, "state");

        var result = BoundedProcessRunner.Run(
            "env",
            [
                $"STRATALINT_REPORT_METRICS_LOG={metrics}",
                $"STRATALINT_SUPERVISOR_ROOT={state}",
                fixture.Supervisor,
                "--role", "scribe-consumer",
                "--", "/usr/bin/true",
            ],
            caller.Path,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Single(File.ReadAllLines(metrics));
    }

    [Theory]
    [InlineData("", "null")]
    [InlineData("unavailable", "null")]
    [InlineData("0.125000", "0.125000")]
    public void ResourceMetricNumbersFailClosedToJsonNull(string sample, string expected)
    {
        using var fixture = new ReportSupervisorFixture();
        var library = Path.Combine(
            fixture.RepositoryRoot,
            "Meta", "StrataLint", "scripts", "perf-event-lib.sh");

        var result = BoundedProcessRunner.Run(
            "bash",
            [
                "-c",
                "source \"$1\"; perf_json_nonnegative_number_or_null \"$2\"",
                "bash",
                library,
                sample,
            ],
            fixture.Root,
            TimeSpan.FromSeconds(10),
            4096);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(expected, Encoding.UTF8.GetString(result.StandardOutput));
    }

    [Fact]
    public void DependencyProbeRemovesPrivateRunDirectoryOnEverySupportedHost()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.RunWithEnvironment(
            "scribe-consumer",
            leanSlot: false,
            fixture.ScratchWriter,
            "PATH=/bin:/usr/bin");

        Assert.Equal(Directory.Exists("/proc") ? 0 : 2, result.ExitCode);
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
    public void EmptyPublishedReclaimGuardOwnerFailsImmediately()
    {
        using var fixture = new ReportSupervisorFixture();
        var guard = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock.reclaim-guard");
        Directory.CreateDirectory(guard);
        File.WriteAllText(Path.Combine(guard, "owner"), "\n", new UTF8Encoding(false));
        var stopwatch = Stopwatch.StartNew();

        var result = fixture.RunWithEnvironment(
            "lean-producer",
            leanSlot: true,
            fixture.ScratchWriter,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=5");
        stopwatch.Stop();

        Assert.Equal(2, result.ExitCode);
        Assert.True(
            stopwatch.Elapsed < TimeSpan.FromSeconds(2),
            $"malformed reclaim guard was polled for {stopwatch.Elapsed}");
        Assert.True(Directory.Exists(guard));
    }

    [Fact]
    public void LockOwnedByADeadProcessIsReclaimed()
    {
        using var fixture = new ReportSupervisorFixture();
        var deadLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(deadLock);
        File.WriteAllText(
            Path.Combine(deadLock, "owner"),
            "99999999|definitely-dead|0\n",
            new UTF8Encoding(false));
        AttachEmptyProcessGroup(fixture.Root, deadLock);

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
            $"{Environment.ProcessId}|not-the-current-process-start|0\n",
            new UTF8Encoding(false));
        AttachEmptyProcessGroup(fixture.Root, reusedLock);

        var result = fixture.Run("lean-producer", leanSlot: true, fixture.ScratchWriter);

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void AbandonedOwnerlessSlotIsNotGuessedDeadAfterInitializationGrace()
    {
        using var fixture = new ReportSupervisorFixture();
        var abandonedLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(abandonedLock);
        Directory.SetLastWriteTimeUtc(abandonedLock, DateTime.UtcNow.AddMinutes(-1));

        var result = fixture.RunWithEnvironment(
            "lean-producer",
            leanSlot: true,
            fixture.ScratchWriter,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(Directory.Exists(abandonedLock));
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
    public void MetricsCommitFailureDoesNotChangeWorkerOutcome()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.RunWithEnvironment(
            "scribe-consumer",
            leanSlot: false,
            fixture.ScratchWriter,
            $"STRATALINT_REPORT_METRICS_LOG={fixture.Root}");

        Assert.Equal(0, result.ExitCode);
        Assert.DoesNotContain(
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

        Assert.Equal(0, result.ExitCode);
        Assert.True(File.Exists(fixture.MetricsLog));
        Assert.Equal(original, File.ReadAllBytes(fixture.MetricsLog));
        Assert.DoesNotContain(
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

        Assert.Equal(0, result.ExitCode);
        Assert.True(Directory.Exists(liveLock));
    }

    [Fact]
    public void HangingBuildIsTerminatedAtTheBuildTimeoutReleasingTheLeanSlot()
    {
        using var fixture = new ReportSupervisorFixture();
        var stopwatch = Stopwatch.StartNew();

        // The worker hangs far beyond the build budget while holding the lean slot.
        // Without a wall-clock build bound the supervisor loops on the live child
        // forever, never reaching finish() (which releases the slot) — this is #403,
        // where lean-report builds hung for hours starving all subsequent builds.
        var result = fixture.RunWithEnvironment(
            "lean-producer",
            leanSlot: true,
            fixture.LongRunningWorker,
            "STRATALINT_BUILD_TIMEOUT_SECONDS=2");
        stopwatch.Stop();

        // The supervisor must abort the hung build near its 2s budget, well inside
        // the fixture's 30s process bound, and surface the timeout exit code.
        Assert.True(
            stopwatch.Elapsed < TimeSpan.FromSeconds(20),
            $"supervisor ignored the build timeout (elapsed {stopwatch.Elapsed})");
        Assert.Equal(124, result.ExitCode);
        Assert.Contains(
            "exceeded",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.OrdinalIgnoreCase);

        // The lean slot lock must be released so subsequent builds are not starved.
        var slots = Path.Combine(fixture.StateRoot, "slots");
        Assert.False(
            Directory.Exists(slots) && Directory.GetDirectories(slots).Length > 0,
            "lean slot lock was not released after the build timeout");
    }

    [Fact]
    public void BuildTimeoutOfZeroKeepsTheLegacyUnboundedBehaviorForFastBuilds()
    {
        using var fixture = new ReportSupervisorFixture();

        // 0 opts out of the wall-clock bound (legacy behavior); a fast worker still
        // completes cleanly and the slot is released via finish() as before.
        var result = fixture.RunWithEnvironment(
            "lean-producer",
            leanSlot: true,
            fixture.ScratchWriter,
            "STRATALINT_BUILD_TIMEOUT_SECONDS=0");

        Assert.Equal(0, result.ExitCode);
        var slots = Path.Combine(fixture.StateRoot, "slots");
        Assert.False(
            Directory.Exists(slots) && Directory.GetDirectories(slots).Length > 0,
            "lean slot lock was not released after a clean build");
    }

    [Fact]
    public void MetricsAppendDelegatesToTheCanonicalPerformanceWriter()
    {
        using var fixture = new ReportSupervisorFixture();
        var source = File.ReadAllText(fixture.Supervisor);

        Assert.Contains("perf_flush_events", source, StringComparison.Ordinal);
        Assert.DoesNotContain("syswrite", source, StringComparison.Ordinal);
    }

    [Fact]
    public void DefaultLeanSlotSerializesConcurrentProducers()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = BoundedProcessRunner.Run(
            "bash",
            [fixture.ConcurrentDriver, fixture.Supervisor, fixture.ProducerWorker,
             fixture.MetricsLog, fixture.StateRoot, fixture.ActiveMarker, fixture.OverlapMarker,
             fixture.ConcurrentRelease, $"{fixture.Root}:{fixture.HostPath}"],
            fixture.Root,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

        Assert.True(
            result.ExitCode == 0,
            $"exit: {result.ExitCode}\n"
            + $"stdout: {Encoding.UTF8.GetString(result.StandardOutput)}\n"
            + $"stderr: {Encoding.UTF8.GetString(result.StandardError)}");
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
                && new FileInfo(fixture.DetachedPid).Length > 0
                && File.Exists(fixture.DetachedParentPid)
                && new FileInfo(fixture.DetachedParentPid).Length > 0
                && File.Exists(Path.Combine(
                    fixture.StateRoot, "slots", "slot-1.lock", "group"))
                && File.Exists(Path.Combine(
                    fixture.StateRoot, "slots", "slot-1.lock", "marker")),
            TimeSpan.FromSeconds(10)));
        var detached = int.Parse(
            File.ReadAllText(fixture.DetachedPid).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);
        var detachedParent = int.Parse(
            File.ReadAllText(fixture.DetachedParentPid).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);
        Assert.True(SpinWait.SpinUntil(
            () => fixture.HasRecordedProcessCandidate(detached),
            TimeSpan.FromSeconds(10)));

        try
        {
            File.WriteAllText(fixture.DetachedRelease, string.Empty, new UTF8Encoding(false));
            Assert.True(SpinWait.SpinUntil(
                () => !ProcessExists(detachedParent) && ProcessExists(detached),
                TimeSpan.FromSeconds(10)));

            var signal = BoundedProcessRunner.Run(
                "/bin/kill",
                ["-TERM", process.Id.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                fixture.Root,
                TimeSpan.FromSeconds(10),
                4096);
            Assert.Equal(0, signal.ExitCode);
            Assert.True(SpinWait.SpinUntil(
                () => process.HasExited,
                TimeSpan.FromSeconds(10)));
            Assert.True(SpinWait.SpinUntil(
                () => !ProcessExists(detached),
                TimeSpan.FromSeconds(10)));
            Assert.False(ProcessExists(detached));
        }
        finally
        {
            if (ProcessExists(detached))
            {
                _ = BoundedProcessRunner.Run(
                    "/bin/kill",
                    ["-KILL", detached.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                    fixture.Root,
                    TimeSpan.FromSeconds(5),
                    4096);
            }
        }
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

    private static void AttachEmptyProcessGroup(string root, string slot)
    {
        var marker = Path.Combine(root, "synthetic-process.marker");
        File.WriteAllText(marker, string.Empty, new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(slot, "marker"),
            marker + "\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(slot, "group"),
            $"99999999|99999999|{EmptyGroupLeaderStartIdentity()}\n",
            new UTF8Encoding(false));
    }

    private static string EmptyGroupLeaderStartIdentity()
    {
        if (!Directory.Exists("/proc")) return "synthetic-dead";
        var stat = File.ReadAllText(Path.Combine(
            "/proc",
            Environment.ProcessId.ToString(System.Globalization.CultureInfo.InvariantCulture),
            "stat"));
        var commandEnd = stat.LastIndexOf(')');
        Assert.True(commandEnd >= 0 && commandEnd + 2 < stat.Length);
        var fields = stat[(commandEnd + 2)..].Split(
            ' ', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
        Assert.True(fields.Length >= 20);
        Assert.Matches("^[1-9][0-9]*$", fields[19]);
        return fields[19];
    }

    private static bool ProcessExists(int pid)
    {
        var result = BoundedProcessRunner.Run(
            "/bin/kill",
            ["-0", pid.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            Directory.GetCurrentDirectory(),
            TimeSpan.FromSeconds(5),
            4096);
        if (result.ExitCode != 0) return false;
        if (Directory.Exists("/proc"))
        {
            try
            {
                var statPath = Path.Combine(
                    "/proc",
                    pid.ToString(System.Globalization.CultureInfo.InvariantCulture),
                    "stat");
                return File.Exists(statPath)
                    && ProcStatRepresentsRunning(File.ReadAllText(statPath));
            }
            catch (IOException)
            {
                return true;
            }
            catch (UnauthorizedAccessException)
            {
                return true;
            }
        }
        try
        {
            using var process = Process.GetProcessById(pid);
            return !process.HasExited;
        }
        catch (ArgumentException)
        {
            return false;
        }
        catch (InvalidOperationException)
        {
            return true;
        }
    }

    private static bool ProcStatRepresentsRunning(string stat)
    {
        var commandEnd = stat.LastIndexOf(')');
        if (commandEnd < 0 || commandEnd + 2 >= stat.Length) return true;
        return stat[commandEnd + 2] is not ('Z' or 'X');
    }
}
