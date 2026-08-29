using System.Diagnostics;
using System.Text;

namespace StrataLint.ScriptTests;

[ScriptSubject("tools/scripts/report/report-supervisor.sh")]
public sealed class ReportSupervisorScriptTests
{
    [Fact]
    public void MissingReportConsumptionFailsClosedWithProducerInstruction()
    {
        using var fixture = new ReportSupervisorFixture();
        var consumer = Path.Combine(
            fixture.RepositoryRoot,
            "tools", "scripts", "report", "report-consumer.sh");

        var result = fixture.RunExternalProcess(
            "bash",
            [consumer, "--role", "ingest-consumer", "--report", Path.Combine(fixture.Root, "missing.json"),
             "--", "/usr/bin/true"],
            maximumOutputBytes: 1024 * 1024);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(
            "make lean-report",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void EachRunUsesIndependentScratch()
    {
        using var fixture = new ReportSupervisorFixture();

        var first = fixture.RunWithEnvironment(
            "scribe-consumer", leanSlot: false, fixture.ScratchWriter, "CI=false");
        var second = fixture.RunWithEnvironment(
            "ingest-consumer", leanSlot: false, fixture.ScratchWriter, "CI=false");

        Assert.Equal(0, first.ExitCode);
        Assert.Equal(0, second.ExitCode);
        var scratchPaths = File.ReadAllLines(fixture.ScratchRecord);
        Assert.Equal(2, scratchPaths.Length);
        Assert.NotEqual(scratchPaths[0], scratchPaths[1]);
        Assert.All(scratchPaths, path => Assert.Contains("/scratch", path, StringComparison.Ordinal));
        Assert.All(scratchPaths, path => Assert.False(Directory.Exists(path)));

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
    public void WorkerFailurePreservesItsExitCode()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.Run("ingest-consumer", leanSlot: false, "/usr/bin/false");

        Assert.Equal(1, result.ExitCode);
    }

    [Fact]
    public void VanishedLsofCandidateDoesNotKillSupervisorOrHealthyChild()
    {
        if (Directory.Exists("/proc")) return;
        using var fixture = new ReportSupervisorFixture();
        fixture.InstallLsofRaceHarness();

        var result = fixture.Run(
            "lean-producer",
            leanSlot: false,
            fixture.LsofRaceWorker);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("completed\n", ReadFixtureText(fixture.ScratchRecord));
        Assert.NotEmpty(File.ReadAllLines(fixture.FailingLsofInvocation));
    }

    [Fact]
    public void ResourceObservationPreservesDiskFdAndRssIncidentFields()
    {
        using var fixture = new ReportSupervisorFixture();

        var result = fixture.Run("scribe-consumer", leanSlot: false, fixture.ScratchWriter);

        Assert.Equal(0, result.ExitCode);
        var observation = Encoding.UTF8.GetString(result.StandardError)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Single(line => line.StartsWith("RESOURCE_OBSERVATION stage=report-supervisor-", StringComparison.Ordinal));
        Assert.Matches(@"disk_free_kb=[0-9]+", observation);
        Assert.Matches(@"fd_soft_limit=[0-9]+", observation);
        Assert.Matches(@"fd_peak=[0-9]+", observation);
        Assert.Matches(@"rss_peak_kb=[0-9]+", observation);
    }

    [Fact]
    public void OwnerlessSlotIsNeverGuessedStale()
    {
        using var fixture = new ReportSupervisorFixture();
        var ownerlessLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(ownerlessLock);
        Directory.SetLastWriteTimeUtc(ownerlessLock, new DateTime(2100, 1, 1, 0, 0, 0, DateTimeKind.Utc));
        var result = fixture.RunWithEnvironment(
            "lean-producer",
            leanSlot: true,
            fixture.ScratchWriter,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1", "STRATALINT_LEAN_MAX_CONCURRENCY=1",
            fixture.ClockEnvironment);

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
        Directory.SetLastWriteTimeUtc(
            abandonedLock,
            new DateTime(2000, 1, 1, 0, 0, 0, DateTimeKind.Utc));

        var result = fixture.RunWithEnvironment(
            "lean-producer", leanSlot: true, fixture.ScratchWriter, fixture.ClockEnvironment);

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void LiveSlotTimeoutIdentifiesHolderDurationAndCommand()
    {
        using var fixture = new ReportSupervisorFixture();
        var ownerPid = Environment.ProcessId.ToString(
            System.Globalization.CultureInfo.InvariantCulture);
        var ownerStart = $"synthetic-start-{ownerPid}";
        var liveLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(liveLock);
        File.WriteAllText(
            Path.Combine(liveLock, "owner"),
            $"{ownerPid}|{ownerStart}\n",
            new UTF8Encoding(false));
        Directory.SetLastWriteTimeUtc(
            liveLock,
            new DateTime(2000, 1, 1, 0, 0, 0, DateTimeKind.Utc));

        var result = fixture.RunWithEnvironment(
            "lean-producer",
            leanSlot: true,
            fixture.ScratchWriter,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1", "STRATALINT_LEAN_MAX_CONCURRENCY=1",
            fixture.ClockEnvironment);

        var stderr = Encoding.UTF8.GetString(result.StandardError);
        Assert.True(
            result.ExitCode == 2,
            $"expected timeout exit 2, got {result.ExitCode}; stderr: {stderr}");
        Assert.Contains("timed out waiting for a Lean slot", stderr, StringComparison.Ordinal);
        Assert.Contains("slot-1", stderr, StringComparison.Ordinal);
        Assert.True(
            stderr.Contains($"pid={ownerPid}", StringComparison.Ordinal),
            $"timeout diagnostic did not name the owner; stderr: {stderr}");
        Assert.Contains($"since={ownerStart}", stderr, StringComparison.Ordinal);
        Assert.Contains("held_for=", stderr, StringComparison.Ordinal);
        Assert.Contains($"command=synthetic-command-{ownerPid}", stderr, StringComparison.Ordinal);
    }

    [Fact]
    public void UnobservableHolderIdentityDuringTimeoutReportingFailsClosed()
    {
        using var fixture = new ReportSupervisorFixture();
        var ownerPid = Environment.ProcessId.ToString(
            System.Globalization.CultureInfo.InvariantCulture);
        var liveLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(liveLock);
        File.WriteAllText(
            Path.Combine(liveLock, "owner"),
            $"{ownerPid}|synthetic-start-{ownerPid}\n",
            new UTF8Encoding(false));

        var result = fixture.RunWithEnvironment(
            "lean-producer",
            leanSlot: true,
            fixture.ScratchWriter,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1", "STRATALINT_LEAN_MAX_CONCURRENCY=1",
            fixture.ClockEnvironment, "STRATALINT_TEST_PS_FAIL_AFTER_COMMAND=1");

        Assert.Equal(2, result.ExitCode);
        var stderr = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("holder identity unavailable", stderr, StringComparison.Ordinal);
        Assert.DoesNotContain("recorded holder exited", stderr, StringComparison.Ordinal);
        Assert.DoesNotContain("held_for=", stderr, StringComparison.Ordinal);
    }

    [Fact]
    public async Task HolderExitDuringTimeoutReportingIsStatedPlainly()
    {
        using var fixture = new ReportSupervisorFixture();
        using var owner = fixture.StartSentinelBlockedProcess();
        var ownerPid = owner.Id.ToString(System.Globalization.CultureInfo.InvariantCulture);
        var liveLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(liveLock);
        File.WriteAllText(
            Path.Combine(liveLock, "owner"),
            $"{ownerPid}|synthetic-start-{ownerPid}\n",
            new UTF8Encoding(false));
        var observed = Path.Combine(fixture.Root, "ps-command-observed");
        var release = Path.Combine(fixture.Root, "ps-command-release");
        var waiter = Task.Run(() => fixture.RunWithEnvironment(
            "lean-producer", leanSlot: true, fixture.ScratchWriter,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1", "STRATALINT_LEAN_MAX_CONCURRENCY=1",
            fixture.ClockEnvironment, "STRATALINT_TEST_PS_PAUSE_ON_COMMAND=1"));
        try
        {
            fixture.WaitUntil(() => File.Exists(observed), "timeout diagnostics did not inspect owner command");
            owner.Kill();
            owner.WaitForExit();
            File.WriteAllText(release, string.Empty, new UTF8Encoding(false));
            var result = await waiter;
            Assert.Equal(2, result.ExitCode);
            var stderr = Encoding.UTF8.GetString(result.StandardError);
            Assert.Contains("recorded holder exited", stderr, StringComparison.Ordinal);
            Assert.DoesNotContain("held_for=", stderr, StringComparison.Ordinal);
        }
        finally
        {
            File.WriteAllText(release, string.Empty, new UTF8Encoding(false));
            if (!owner.HasExited) owner.Kill(entireProcessTree: true);
        }
    }

    [Fact]
    public void HangingBuildIsTerminatedAtTheBuildTimeoutReleasingTheLeanSlot()
    {
        using var fixture = new ReportSupervisorFixture();

        // The worker hangs far beyond the build budget while holding the lean slot.
        // Without a wall-clock build bound the supervisor loops on the live child
        // forever, never reaching finish() (which releases the slot) — this is #403,
        // where lean-report builds hung for hours starving all subsequent builds.
        var result = fixture.RunWithEnvironment(
            "lean-producer",
            leanSlot: true,
            fixture.LongRunningWorker,
            "STRATALINT_BUILD_TIMEOUT_SECONDS=2", fixture.ClockEnvironment);

        // The fixture's five-minute process bound is only a runaway guard. The
        // verdict comes from the supervisor's state transition and artifacts.
        Assert.True(
            result.ExitCode == 124,
            $"expected timeout exit 124, got {result.ExitCode}; stderr: "
                + Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains(
            "exceeded",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.OrdinalIgnoreCase);
        Assert.True(fixture.ClockReads > 0, "the injected supervisor clock was not read");
        var grandchild = int.Parse(
            ReadFixtureText(fixture.ScratchRecord).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);
        fixture.WaitUntil(
            () => !ProcessExists(grandchild),
            "timed-out worker process tree survived supervisor termination");
        Assert.False(
            ProcessExists(grandchild),
            $"timed-out worker grandchild {grandchild} is still running");

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
    public void TerminationReapsTheWorkerProcessTree()
    {
        using var fixture = new ReportSupervisorFixture();
        using var process = fixture.StartLongRunningProducer();
        fixture.WaitUntil(
            () => File.Exists(fixture.GrandchildPid)
                && new FileInfo(fixture.GrandchildPid).Length > 0,
            "worker did not publish its child pid");
        var grandchild = int.Parse(
            ReadFixtureText(fixture.GrandchildPid).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        var signal = fixture.RunExternalProcess(
            "/bin/kill",
            ["-TERM", process.Id.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            maximumOutputBytes: 4096);
        Assert.Equal(0, signal.ExitCode);
        fixture.WaitForExit(process, "supervisor did not exit after SIGTERM");

        fixture.WaitUntil(
            () => !ProcessExists(grandchild),
            "supervisor did not reap the worker process tree");
        Assert.False(ProcessExists(grandchild));
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
            ReadFixtureText(fixture.ExitedGrandchildPid).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        try
        {
            fixture.WaitUntil(
                () => !ProcessExists(grandchild),
                "supervisor did not reap the background descendant");
        }
        finally
        {
            if (ProcessExists(grandchild))
            {
                _ = fixture.RunExternalProcess(
                    "/bin/kill",
                    ["-KILL", grandchild.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                    maximumOutputBytes: 4096);
            }
        }
    }

    [Fact]
    public void TerminationReapsADescendantThatCreatesANewSession()
    {
        using var fixture = new ReportSupervisorFixture();
        using var process = fixture.StartDetachedProducer();
        using var watchdog = new ReportSupervisorTestWatchdog(fixture.SafetyTimeout);
        watchdog.Track(process);
        int? detached = null;
        try
        {
            fixture.WaitUntil(
                () => File.Exists(fixture.DetachedPid)
                    && new FileInfo(fixture.DetachedPid).Length > 0
                    && File.Exists(fixture.DetachedParentPid)
                    && new FileInfo(fixture.DetachedParentPid).Length > 0,
                "detached worker did not publish its process topology");
            detached = int.Parse(
                ReadFixtureText(fixture.DetachedPid).Trim(),
                System.Globalization.CultureInfo.InvariantCulture);
            var detachedParent = int.Parse(
                ReadFixtureText(fixture.DetachedParentPid).Trim(),
                System.Globalization.CultureInfo.InvariantCulture);

            fixture.WaitUntil(
                () => fixture.HasRecordedProcessCandidate(detached.Value),
                "supervisor did not record the session-changing descendant");

            File.WriteAllText(fixture.DetachedParentRelease, string.Empty, new UTF8Encoding(false));
            fixture.WaitUntil(
                () => !ProcessExists(detachedParent) && ProcessExists(detached.Value),
                "detached child did not outlive its helper parent");

            var signal = fixture.RunExternalProcess(
                "/bin/kill",
                ["-TERM", process.Id.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                maximumOutputBytes: 4096);
            Assert.Equal(0, signal.ExitCode);
            fixture.WaitUntil(
                () => process.HasExited,
                "supervisor did not exit after SIGTERM");
            fixture.WaitUntil(
                () => !ProcessExists(detached.Value),
                "recorded session-changing descendant survived supervisor termination");
        }
        finally
        {
            TerminateForTestCleanup(process, fixture);
            if (detached.HasValue && ProcessExists(detached.Value))
            {
                _ = fixture.RunExternalProcess(
                    "/bin/kill",
                    ["-KILL", detached.Value.ToString(
                        System.Globalization.CultureInfo.InvariantCulture)],
                    maximumOutputBytes: 4096);
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
            ReadFixtureText(fixture.DoubleForkPid).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        fixture.WaitUntil(
            () => !ProcessExists(detached),
            "supervisor did not reap the double-forked session");
        Assert.False(ProcessExists(detached));
    }

    private static bool ProcessExists(int pid)
    {
        var result = TestProcessRunner.Run(
            "/bin/kill",
            ["-0", pid.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            Directory.GetCurrentDirectory(),
            TestBudgets.ShortProcessHangGuard,
            4096);
        if (result.ExitCode != 0) return false;
        if (Directory.Exists("/proc"))
        {
            try
            {
                var stat = ReadFixtureText(Path.Combine(
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

    private static string ReadFixtureText(string path)
    {
        using var reader = new StreamReader(path);
        return reader.ReadToEnd();
    }

    private static void TerminateForTestCleanup(
        Process process,
        ReportSupervisorFixture fixture)
    {
        try
        {
            if (!process.HasExited) process.Kill(entireProcessTree: true);
            fixture.WaitForExit(process, "test cleanup could not terminate the supervisor");
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

}
