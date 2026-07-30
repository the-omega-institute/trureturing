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
                $"STRATALINT_PERF_CONFIGURATION={fixture.PerformanceConfiguration}",
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
    public void PerformanceWriterUsesTheCallersBuildConfiguration()
    {
        using var temporary = new TemporaryDirectory();
        var root = FindRepositoryRoot();
        var library = Path.Combine(root, "Meta", "StrataLint", "scripts", "perf-event-lib.sh");
        var spool = Path.Combine(temporary.Path, "events.jsonl");
        var target = Path.Combine(temporary.Path, "StrataLint.dll");
        var invocations = Path.Combine(temporary.Path, "dotnet-invocations.txt");
        var dotnet = Path.Combine(temporary.Path, "dotnet");
        File.WriteAllText(spool, "{}\n", new UTF8Encoding(false));
        File.WriteAllText(target, string.Empty, new UTF8Encoding(false));
        File.WriteAllText(dotnet, $$"""
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' "$*" >> "{{invocations}}"
            if [[ "$1" == "msbuild" ]]; then printf '%s\n' "{{target}}"; fi
            """ + "\n", new UTF8Encoding(false));
        var chmod = BoundedProcessRunner.Run(
            "chmod", ["+x", dotnet], temporary.Path, TimeSpan.FromSeconds(10), 4096);
        Assert.Equal(0, chmod.ExitCode);

        var result = BoundedProcessRunner.Run(
            "env",
            [
                $"PATH={temporary.Path}:{Environment.GetEnvironmentVariable("PATH")}",
                "STRATALINT_PERF_CONFIGURATION=Debug",
                "bash", "-c", "source \"$1\"; perf_flush_events \"$2\" \"$3\"",
                "bash", library, root, spool,
            ],
            temporary.Path,
            TimeSpan.FromSeconds(10),
            4096);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "-property:Configuration=Debug",
            File.ReadAllText(invocations),
            StringComparison.Ordinal);
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
    public void VanishedLsofCandidateDoesNotKillSupervisorOrHealthyChild()
    {
        if (Directory.Exists("/proc")) return;
        using var fixture = new ReportSupervisorFixture();
        fixture.InstallFailingLsof();

        var result = fixture.Run(
            "lean-producer",
            leanSlot: false,
            fixture.LsofRaceWorker);

        Assert.True(
            result.ExitCode == 0,
            $"supervisor exited {result.ExitCode}; stderr: "
                + Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal("completed\n", File.ReadAllText(fixture.ScratchRecord));
        Assert.True(
            File.Exists(fixture.FailingLsofInvocation),
            "the fake lsof was not invoked");
        Assert.NotEmpty(File.ReadAllLines(fixture.FailingLsofInvocation));
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
        Assert.True(
            result.ExitCode == 124,
            $"expected timeout exit 124, got {result.ExitCode}; stderr: "
                + Encoding.UTF8.GetString(result.StandardError));
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
             fixture.PerformanceConfiguration],
            fixture.Root,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

        Assert.True(
            result.ExitCode == 0,
            $"concurrent driver exited {result.ExitCode}; stdout: "
                + Encoding.UTF8.GetString(result.StandardOutput)
                + "; stderr: "
                + Encoding.UTF8.GetString(result.StandardError));
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
        using var watchdog = new ReportSupervisorTestWatchdog(TimeSpan.FromSeconds(45));
        watchdog.Track(process);
        int? detached = null;
        try
        {
            Assert.True(SpinWait.SpinUntil(
                () => File.Exists(fixture.DetachedPid)
                    && new FileInfo(fixture.DetachedPid).Length > 0
                    && File.Exists(fixture.DetachedParentPid)
                    && new FileInfo(fixture.DetachedParentPid).Length > 0,
                TimeSpan.FromSeconds(10)),
                "detached worker did not publish its process topology");
            detached = int.Parse(
                File.ReadAllText(fixture.DetachedPid).Trim(),
                System.Globalization.CultureInfo.InvariantCulture);
            var detachedParent = int.Parse(
                File.ReadAllText(fixture.DetachedParentPid).Trim(),
                System.Globalization.CultureInfo.InvariantCulture);

            Assert.True(SpinWait.SpinUntil(
                () => fixture.HasRecordedProcessCandidate(detached.Value),
                TimeSpan.FromSeconds(10)),
                "supervisor did not record the session-changing descendant");

            File.WriteAllText(fixture.DetachedRelease, string.Empty, new UTF8Encoding(false));
            Assert.True(SpinWait.SpinUntil(
                () => !ProcessExists(detachedParent) && ProcessExists(detached.Value),
                TimeSpan.FromSeconds(10)),
                "detached child did not outlive its helper parent");

            var signal = BoundedProcessRunner.Run(
                "/bin/kill",
                ["-TERM", process.Id.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                fixture.Root,
                TimeSpan.FromSeconds(10),
                4096);
            Assert.Equal(0, signal.ExitCode);
            Assert.True(SpinWait.SpinUntil(
                () => process.HasExited,
                TimeSpan.FromSeconds(10)),
                "supervisor did not exit after SIGTERM");
            Assert.True(SpinWait.SpinUntil(
                () => !ProcessExists(detached.Value),
                TimeSpan.FromSeconds(10)),
                "recorded session-changing descendant survived supervisor termination");
        }
        finally
        {
            TerminateForTestCleanup(process);
            if (detached.HasValue && ProcessExists(detached.Value))
            {
                _ = BoundedProcessRunner.Run(
                    "/bin/kill",
                    ["-KILL", detached.Value.ToString(
                        System.Globalization.CultureInfo.InvariantCulture)],
                    fixture.Root,
                    TimeSpan.FromSeconds(5),
                    4096);
            }
        }
    }

    [Fact]
    public void ProcessExistenceTreatsAnUnreapedChildAsTerminated()
    {
        // On macOS, the non-/proc Process API can expose an unreaped child as
        // not exited but threadless. Linux excludes Z/X states through /proc
        // before reaching this predicate.
        Assert.False(
            IsLiveNonProcProcess(hasExited: false, threadCount: 0),
            "an exited, threadless child is not a live process");
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
        if (result.ExitCode != 0) return false;
        if (Directory.Exists("/proc"))
        {
            try
            {
                var stat = File.ReadAllText(Path.Combine(
                    "/proc",
                    pid.ToString(System.Globalization.CultureInfo.InvariantCulture),
                    "stat"));
                var commandEnd = stat.LastIndexOf(')');
                return commandEnd < 0
                    || commandEnd + 2 >= stat.Length
                    || stat[commandEnd + 2] is not ('Z' or 'X');
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
            return IsLiveNonProcProcess(process.HasExited, process.Threads.Count);
        }
        catch (ArgumentException)
        {
            return false;
        }
        catch (InvalidOperationException)
        {
            return true;
        }
        catch (System.ComponentModel.Win32Exception)
        {
            return true;
        }
    }

    private static bool IsLiveNonProcProcess(bool hasExited, int threadCount) =>
        !hasExited && threadCount > 0;

    private static void TerminateForTestCleanup(Process process)
    {
        try
        {
            if (!process.HasExited) process.Kill(entireProcessTree: true);
            _ = process.WaitForExit(5_000);
        }
        catch (InvalidOperationException)
        {
            // The process exited concurrently with cleanup.
        }
        catch (System.ComponentModel.Win32Exception)
        {
            // The detached PID fallback below remains available to the test.
        }
    }

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
