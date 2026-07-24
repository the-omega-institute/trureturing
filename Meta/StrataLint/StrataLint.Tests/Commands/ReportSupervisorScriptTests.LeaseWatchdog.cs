using System.Diagnostics;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReportSupervisorScriptTests
{
    [Fact]
    public void ExpiredCanonicalLeaseWithoutProducerFenceIsNotReclaimed()
    {
        using var fixture = new LeaseWatchdogFixture();
        fixture.CreateTimestampedSlotOwnedByCurrentProcess(
            DateTimeOffset.UtcNow.AddMinutes(-1).ToUnixTimeMilliseconds());

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LEAN_SLOT_LEASE_SECONDS=5",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=3");

        Assert.Equal(2, result.ExitCode);
        Assert.True(fixture.SlotExists());
    }

    [Fact]
    public void UnreadableLiveOwnerIdentityIsNotGuessedStale()
    {
        using var fixture = new LeaseWatchdogFixture();
        var slot = fixture.CreateSlotOwnedByCurrentProcess();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.Root}:/bin:/usr/bin:/usr/sbin:/sbin",
            $"STRATALINT_TEST_PS_FAIL_PID={Environment.ProcessId}",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(Directory.Exists(slot));
    }

    [Fact]
    public void ClaimantFallsBackToTimestampedLeaseWhenItsStartIdentityIsUnreadable()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.Root}:/bin:/usr/bin:/usr/sbin:/sbin",
            "STRATALINT_TEST_PS_FAIL_ALL=1",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void OneSecondLeaseIsRejectedAsTooShortForSafeRenewal()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LEAN_SLOT_LEASE_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(
            "must be 5..86400",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void FiveSecondLeaseRenewsBeforeAConcurrentAcquirerCanReclaimIt()
    {
        using var fixture = new LeaseWatchdogFixture();
        using var holder = fixture.Start(
            fixture.SleepWorker,
            "STRATALINT_LEAN_SLOT_LEASE_SECONDS=5");
        Assert.True(SpinWait.SpinUntil(
            () => fixture.SlotExists() && File.Exists(fixture.SleepWorkerPidFile),
            TimeSpan.FromSeconds(10)));
        var owner = File.ReadAllText(Path.Combine(fixture.Slot, "owner")).Trim().Split('|');
        Assert.Equal(3, owner.Length);
        Assert.True(long.Parse(owner[2], System.Globalization.CultureInfo.InvariantCulture) > 1_000_000_000_000);
        Thread.Sleep(6_500);

        var contender = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LEAN_SLOT_LEASE_SECONDS=5",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=2");

        Assert.Equal(2, contender.ExitCode);
        Assert.False(holder.HasExited);
        var signal = BoundedProcessRunner.Run(
            "/bin/kill",
            ["-TERM", holder.Id.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            fixture.Root,
            TimeSpan.FromSeconds(5),
            4096);
        Assert.Equal(0, signal.ExitCode);
        Assert.True(holder.WaitForExit(5_000));
    }

    [Fact]
    public void SigkillOrphanedHolderReleasesItsLeaseToTheNextAcquirer()
    {
        using var fixture = new LeaseWatchdogFixture();
        using var holder = fixture.Start(fixture.SleepWorker);
        Assert.True(SpinWait.SpinUntil(
            () => fixture.SlotExists() && File.Exists(fixture.SleepWorkerPidFile),
            TimeSpan.FromSeconds(10)));
        var orphanPid = fixture.ReadSleepWorkerPid();

        var signal = BoundedProcessRunner.Run(
            "/bin/kill",
            ["-KILL", holder.Id.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            fixture.Root,
            TimeSpan.FromSeconds(5),
            4096);
        Assert.Equal(0, signal.ExitCode);
        Assert.True(holder.WaitForExit(5_000));
        Assert.True(ProcessExists(orphanPid));

        var result = fixture.Run(fixture.SuccessWorker, "STRATALINT_LOCK_TIMEOUT_SECONDS=3");

        Assert.Equal(0, result.ExitCode);
        Assert.True(SpinWait.SpinUntil(
            () => !ProcessExists(orphanPid),
            TimeSpan.FromSeconds(5)));
        Assert.False(ProcessExists(orphanPid));
    }

    [Fact]
    public void CpuActiveMathlibScalePhaseOutlivingTheStallThresholdIsNeverKilled()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.Run(
            fixture.CpuOnlyWorker,
            "STRATALINT_REPORT_STALL_TIMEOUT_SECONDS=2");

        Assert.Equal(0, result.ExitCode);
        Assert.DoesNotContain(
            "no Lean progress",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void DirectSingleProcessWatchdogFailureReturnsAndRecordsExactlyTwo()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.RunDirectSingleProcess();

        Assert.Equal(2, result.ExitCode);
        Assert.Equal(2, fixture.ReadSingleMetricExitCode());
    }

    [Fact]
    public void ManualBashInvocationWatchdogFailureReturnsAndRecordsExactlyTwo()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.RunManualSingleProcess();

        Assert.Equal(2, result.ExitCode);
        Assert.Equal(2, fixture.ReadSingleMetricExitCode());
    }

    [Fact]
    public void LiveLegacyPidAndStartOwnerIsNeverExpired()
    {
        using var fixture = new LeaseWatchdogFixture();
        var slot = fixture.CreateSlotOwnedByCurrentProcess();
        File.SetLastWriteTimeUtc(Path.Combine(slot, "owner"), DateTime.UtcNow.AddMinutes(-1));

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LEAN_SLOT_LEASE_SECONDS=5",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(Directory.Exists(slot));
    }

    [Fact]
    public void LiveLegacyPidOwnerIsNeverExpired()
    {
        using var fixture = new LeaseWatchdogFixture();
        var slot = fixture.CreateSlotWithOwner($"{Environment.ProcessId}\n");
        File.SetLastWriteTimeUtc(Path.Combine(slot, "owner"), DateTime.UtcNow.AddMinutes(-1));

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LEAN_SLOT_LEASE_SECONDS=5",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(Directory.Exists(slot));
    }

    [Fact]
    public void MalformedNonemptyOwnerFailsClosed()
    {
        using var fixture = new LeaseWatchdogFixture();
        var slot = fixture.CreateSlotWithOwner("not-an-owner\n");
        Directory.SetLastWriteTimeUtc(slot, DateTime.UtcNow.AddMinutes(-1));

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(Directory.Exists(slot));
    }

    [Fact]
    public void UnknownCanonicalLiveOwnerCannotBeReclaimedOnTimeout()
    {
        using var fixture = new LeaseWatchdogFixture();
        fixture.CreateSlotWithOwner(
            $"{Environment.ProcessId}|unknown|{DateTimeOffset.UtcNow.AddMinutes(-1).ToUnixTimeMilliseconds()}\n");

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LEAN_SLOT_LEASE_SECONDS=5",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(fixture.SlotExists());
    }

    [Fact]
    public void ThreeFieldOwnerWhosePidWasReusedIsReclaimed()
    {
        using var fixture = new LeaseWatchdogFixture();
        fixture.CreateSlotWithOwner(
            $"{Environment.ProcessId}|not-the-current-start|{DateTimeOffset.UtcNow.ToUnixTimeMilliseconds()}\n");
        fixture.AttachEmptyFenceMarker();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.Root}:/bin:/usr/bin:/usr/sbin:/sbin",
            $"STRATALINT_TEST_PS_REUSED_PID={Environment.ProcessId}",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=2");

        Assert.True(
            result.ExitCode == 0,
            $"stdout: {Encoding.UTF8.GetString(result.StandardOutput)}\n"
            + $"stderr: {Encoding.UTF8.GetString(result.StandardError)}");
    }

    [Fact]
    public void OneFailedRenewalWriteIsRetriedInsideTheRemainingLeaseWindow()
    {
        using var fixture = new LeaseWatchdogFixture();
        using var holder = fixture.Start(
            fixture.CpuOnlyWorker,
            $"PATH={fixture.Root}:/bin:/usr/bin:/usr/sbin:/sbin",
            $"STRATALINT_TEST_FAIL_SLOT_OWNER_RENAME={fixture.RenewalFailureTrigger}",
            "STRATALINT_LEAN_SLOT_LEASE_SECONDS=5");
        Assert.True(SpinWait.SpinUntil(
            () => fixture.SlotExists() && File.Exists(fixture.CpuWorkerPidFile),
            TimeSpan.FromSeconds(10)));
        Thread.Sleep(300);
        File.WriteAllText(fixture.RenewalFailureTrigger, "fail once\n", new UTF8Encoding(false));

        Assert.True(holder.WaitForExit(10_000));
        Assert.Equal(0, holder.ExitCode);
        Assert.False(File.Exists(fixture.RenewalFailureTrigger));
    }

    [Fact]
    public void ConcurrentAcquirersSerializeWhenReclaimingTheSameStaleSlot()
    {
        using var fixture = new ReportSupervisorFixture();
        var staleSlot = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        Directory.CreateDirectory(staleSlot);
        File.WriteAllText(
            Path.Combine(staleSlot, "owner"),
            "99999999|definitely-dead|0\n",
            new UTF8Encoding(false));
        var fence = Path.Combine(fixture.Root, "synthetic-process.marker");
        File.WriteAllText(fence, string.Empty, new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(staleSlot, "marker"),
            fence + "\n",
            new UTF8Encoding(false));
        var marker = Path.Combine(fixture.Root, "stale-process.marker");
        File.WriteAllText(marker, string.Empty, new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(staleSlot, "marker"), marker + "\n", new UTF8Encoding(false));

        var result = BoundedProcessRunner.Run(
            "bash",
            [fixture.ConcurrentDriver, fixture.Supervisor, fixture.ProducerWorker,
             fixture.MetricsLog, fixture.StateRoot, fixture.ActiveMarker, fixture.OverlapMarker],
            fixture.Root,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.False(File.Exists(fixture.OverlapMarker));
        Assert.Equal(2, fixture.ReadMetrics().Count);
    }

    [Fact]
    public void StalledProducerIsKilledAsInfrastructureFailureAndReleasesSlot()
    {
        using var fixture = new LeaseWatchdogFixture();

        var stalled = fixture.Run(
            fixture.SleepWorker,
            "STRATALINT_REPORT_STALL_TIMEOUT_SECONDS=2");

        Assert.Equal(2, stalled.ExitCode);
        Assert.Contains(
            "infrastructure failure",
            Encoding.UTF8.GetString(stalled.StandardError),
            StringComparison.OrdinalIgnoreCase);
        Assert.Contains(
            "no Lean progress",
            Encoding.UTF8.GetString(stalled.StandardError),
            StringComparison.Ordinal);
        Assert.False(ProcessExists(fixture.ReadSleepWorkerPid()));
        Assert.False(fixture.SlotExists());
        Assert.Equal(0, fixture.Run(fixture.SuccessWorker).ExitCode);
    }

    [Fact]
    public void NewOleanFilesKeepAQuietProducerAlive()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.Run(
            fixture.OleanProgressWorker,
            "STRATALINT_REPORT_STALL_TIMEOUT_SECONDS=2");

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void PipeOutputKeepsAProducerAliveWithoutOleanChanges()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.Run(
            fixture.PipeProgressWorker,
            "STRATALINT_REPORT_STALL_TIMEOUT_SECONDS=2");

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "progress-4",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ProducerLogOutputKeepsAQuietUncompiledPhaseAlive()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.Run(
            fixture.LogProgressWorker,
            "STRATALINT_REPORT_STALL_TIMEOUT_SECONDS=2");

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void FaultInjectedPartialLakeArtifactIsRebuiltAndImportableOnTheNextBuild()
    {
        using var fixture = new LeaseWatchdogFixture();

        var interrupted = fixture.Run(
            fixture.PartialLakeArtifactWorker,
            "STRATALINT_REPORT_STALL_TIMEOUT_SECONDS=2");

        Assert.Equal(2, interrupted.ExitCode);
        Assert.Equal("partial", File.ReadAllText(fixture.RecoveryOlean));

        fixture.WriteRecoveryLakeProject();
        var rebuild = BoundedProcessRunner.Run(
            "lake", ["build", "Recovery"], fixture.Root,
            TimeSpan.FromSeconds(30), 1024 * 1024);
        Assert.Equal(0, rebuild.ExitCode);
        Assert.True(new FileInfo(fixture.RecoveryOlean).Length > "partial".Length);

        var import = BoundedProcessRunner.Run(
            "lake", ["env", "lean", "Verify.lean"], fixture.Root,
            TimeSpan.FromSeconds(30), 1024 * 1024);
        Assert.Equal(0, import.ExitCode);
    }

    private sealed class LeaseWatchdogFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal LeaseWatchdogFixture()
        {
            SuccessWorker = WriteExecutable("success.sh", "#!/usr/bin/env bash\nexit 0");
            SleepWorker = WriteExecutable("sleep.sh", """
                #!/usr/bin/env bash
                printf '%s\n' "$$" > "$1/sleep-worker.pid"
                sleep 60
                """);
            OleanProgressWorker = WriteExecutable("olean-progress.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                mkdir -p "$1/.lake/build/lib/lean"
                for index in 1 2 3 4; do
                  touch "$1/.lake/build/lib/lean/progress-${index}.olean"
                  sleep 1
                done
                """);
            PipeProgressWorker = WriteExecutable("pipe-progress.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                for index in 1 2 3 4; do
                  printf 'progress-%s\n' "$index"
                  sleep 1
                done
                """);
            LogProgressWorker = WriteExecutable("log-progress.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                mkdir -p "$STRATALINT_LEAN_PROGRESS_LOG_ROOT"
                for index in 1 2 3 4; do
                  printf 'progress-%s\n' "$index" >> "$STRATALINT_LEAN_PROGRESS_LOG_ROOT/build.stdout.log"
                  sleep 1
                done
                """);
            CpuOnlyWorker = WriteExecutable("cpu-only.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                printf '%s\n' "$$" > "$1/cpu-worker.pid"
                perl -MTime::HiRes=time -e '$end = time() + 5; 1 while time() < $end'
                """);
            PartialLakeArtifactWorker = WriteExecutable("partial-lake-artifact.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                mkdir -p "$1/.lake/build/lib/lean"
                printf partial > "$1/.lake/build/lib/lean/Recovery.olean"
                sleep 60
                """);
            _ = WriteExecutable("ps", """
                #!/usr/bin/env bash
                if [[ "${STRATALINT_TEST_PS_FAIL_ALL:-}" == "1" ]]; then exit 1; fi
                previous=""
                for argument in "$@"; do
                  if [[ "$previous" == "-p" && "$argument" == "${STRATALINT_TEST_PS_REUSED_PID:-}" ]]; then
                    printf 'synthetic-current-start\n'
                    exit 0
                  fi
                  if [[ "$previous" == "-p" && "$argument" == "${STRATALINT_TEST_PS_FAIL_PID:-}" ]]; then
                    exit 1
                  fi
                  previous="$argument"
                done
                exec /bin/ps "$@"
                """);
            _ = WriteExecutable("mv", """
                #!/usr/bin/env bash
                set -euo pipefail
                destination="${!#}"
                trigger="${STRATALINT_TEST_FAIL_SLOT_OWNER_RENAME:-}"
                if [[ -n "$trigger" && -f "$trigger" && "$destination" == */slot-1.lock/owner ]]; then
                  /bin/rm -f -- "$trigger"
                  exit 1
                fi
                exec /bin/mv "$@"
                """);
            ManualDriver = WriteExecutable("manual-driver.sh", """
                #!/usr/bin/env bash
                set +e
                stdout="$1"
                stderr="$2"
                shift 2
                "$@" > "$stdout" 2> "$stderr"
                exit "$?"
                """);
        }

        internal string Root => temporary.Path;
        internal string StateRoot => Path.Combine(Root, "state");
        internal string MetricsLog => Path.Combine(Root, "metrics.jsonl");
        internal string Slot => Path.Combine(StateRoot, "slots", "slot-1.lock");
        internal string ProgressLogRoot => Path.Combine(Root, "producer.logs");
        internal string SleepWorkerPidFile => Path.Combine(Root, "sleep-worker.pid");
        internal string CpuWorkerPidFile => Path.Combine(Root, "cpu-worker.pid");
        internal string RenewalFailureTrigger => Path.Combine(Root, "fail-renewal-once");
        internal string RecoveryOlean => Path.Combine(
            Root, ".lake", "build", "lib", "lean", "Recovery.olean");
        internal string ManualStdout => Path.Combine(Root, "manual.stdout");
        internal string ManualStderr => Path.Combine(Root, "manual.stderr");
        internal string SuccessWorker { get; }
        internal string SleepWorker { get; }
        internal string OleanProgressWorker { get; }
        internal string PipeProgressWorker { get; }
        internal string LogProgressWorker { get; }
        internal string CpuOnlyWorker { get; }
        internal string PartialLakeArtifactWorker { get; }
        internal string ManualDriver { get; }

        internal bool SlotExists() => Directory.Exists(Slot);

        internal int ReadSleepWorkerPid() => int.Parse(
            File.ReadAllText(SleepWorkerPidFile).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        internal string CreateSlotOwnedByCurrentProcess()
        {
            Directory.CreateDirectory(Slot);
            var start = BoundedProcessRunner.Run(
                "/bin/ps",
                ["-o", "lstart=", "-p", Environment.ProcessId.ToString(
                    System.Globalization.CultureInfo.InvariantCulture)],
                Root,
                TimeSpan.FromSeconds(5),
                4096);
            Assert.Equal(0, start.ExitCode);
            File.WriteAllText(
                Path.Combine(Slot, "owner"),
                $"{Environment.ProcessId}|{Encoding.UTF8.GetString(start.StandardOutput).Trim()}\n",
                new UTF8Encoding(false));
            return Slot;
        }

        internal void CreateTimestampedSlotOwnedByCurrentProcess(long timestamp)
        {
            _ = CreateSlotOwnedByCurrentProcess();
            var ownerFile = Path.Combine(Slot, "owner");
            var owner = File.ReadAllText(ownerFile).Trim();
            File.WriteAllText(
                ownerFile,
                $"{owner}|{timestamp}\n",
                new UTF8Encoding(false));
        }

        internal string CreateSlotWithOwner(string owner)
        {
            Directory.CreateDirectory(Slot);
            File.WriteAllText(Path.Combine(Slot, "owner"), owner, new UTF8Encoding(false));
            return Slot;
        }

        internal void AttachEmptyFenceMarker()
        {
            var marker = Path.Combine(Root, "synthetic-process.marker");
            File.WriteAllText(marker, string.Empty, new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(Slot, "marker"),
                marker + "\n",
                new UTF8Encoding(false));
        }

        internal ProcessOutput RunDirectSingleProcess() => RunSingleProcess(viaBash: false);

        internal ProcessOutput RunManualSingleProcess() => RunSingleProcess(viaBash: true);

        internal int ReadSingleMetricExitCode()
        {
            var line = Assert.Single(File.ReadAllLines(MetricsLog));
            using var document = System.Text.Json.JsonDocument.Parse(line);
            return document.RootElement.GetProperty("rc").GetInt32();
        }

        internal void WriteRecoveryLakeProject()
        {
            File.WriteAllText(
                Path.Combine(Root, "lean-toolchain"),
                "leanprover/lean4:v4.31.0\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(Root, "lakefile.toml"),
                """
                name = "RecoveryFixture"
                version = "0.1.0"
                defaultTargets = ["Recovery"]

                [[lean_lib]]
                name = "Recovery"
                """ + "\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(Root, "Recovery.lean"),
                "theorem recovered : True := by trivial\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(Root, "Verify.lean"),
                "import Recovery\n#check recovered\n",
                new UTF8Encoding(false));
        }

        internal ProcessOutput Run(string worker, params string[] environment) =>
            BoundedProcessRunner.Run(
                "env",
                Arguments(worker, environment),
                Root,
                TimeSpan.FromSeconds(12),
                1024 * 1024);

        internal Process Start(string worker, params string[] environment)
        {
            var info = new ProcessStartInfo
            {
                FileName = "env",
                WorkingDirectory = Root,
                UseShellExecute = false,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
            };
            foreach (var argument in Arguments(worker, environment)) info.ArgumentList.Add(argument);
            var process = new Process { StartInfo = info };
            Assert.True(process.Start());
            return process;
        }

        public void Dispose()
        {
            if (File.Exists(SleepWorkerPidFile)
                && int.TryParse(File.ReadAllText(SleepWorkerPidFile).Trim(), out var workerPid))
            {
                _ = BoundedProcessRunner.Run(
                    "/bin/kill", ["-KILL", $"-{workerPid}"],
                    Root, TimeSpan.FromSeconds(5), 4096);
            }
            if (Directory.Exists(StateRoot))
            {
                foreach (var ownerFile in Directory.GetFiles(StateRoot, "owner", SearchOption.AllDirectories))
                {
                    var owner = File.ReadAllText(ownerFile).Split('|')[0];
                    if (int.TryParse(owner, out var pid) && pid != Environment.ProcessId)
                    {
                        _ = BoundedProcessRunner.Run(
                            "/bin/kill", ["-KILL", pid.ToString(
                                System.Globalization.CultureInfo.InvariantCulture)],
                            Root, TimeSpan.FromSeconds(5), 4096);
                    }
                }
            }
            temporary.Dispose();
        }

        private IReadOnlyList<string> Arguments(string worker, IReadOnlyList<string> environment)
        {
            var arguments = new List<string>
            {
                $"STRATALINT_REPORT_METRICS_LOG={MetricsLog}",
                $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
                $"STRATALINT_LEAN_PROGRESS_ROOT={Root}",
                $"STRATALINT_LEAN_PROGRESS_LOG_ROOT={ProgressLogRoot}",
                "STRATALINT_REPORT_WATCHDOG_POLL_SECONDS=1",
            };
            arguments.AddRange(environment);
            arguments.Add(Supervisor);
            arguments.Add("--role");
            arguments.Add("lean-producer");
            arguments.Add("--lean-slot");
            arguments.Add("--");
            arguments.Add(worker);
            arguments.Add(Root);
            return arguments;
        }

        private ProcessOutput RunSingleProcess(bool viaBash)
        {
            var arguments = new List<string>
            {
                $"STRATALINT_REPORT_METRICS_LOG={MetricsLog}",
                $"STRATALINT_SUPERVISOR_ROOT={StateRoot}",
                $"STRATALINT_LEAN_PROGRESS_ROOT={Root}",
                "STRATALINT_REPORT_WATCHDOG_POLL_SECONDS=1",
                "STRATALINT_REPORT_STALL_TIMEOUT_SECONDS=2",
            };
            if (viaBash) arguments.Add("bash");
            arguments.Add(Supervisor);
            arguments.Add("--role");
            arguments.Add("lean-producer");
            arguments.Add("--lean-slot");
            arguments.Add("--");
            arguments.Add("/bin/sleep");
            arguments.Add("60");
            if (!viaBash)
            {
                return BoundedProcessRunner.Run(
                    "env", arguments, Root, TimeSpan.FromSeconds(12), 1024 * 1024);
            }
            arguments.Remove("bash");
            arguments.Insert(0, "env");
            arguments.Insert(0, ManualStderr);
            arguments.Insert(0, ManualStdout);
            return BoundedProcessRunner.Run(
                ManualDriver, arguments, Root, TimeSpan.FromSeconds(12), 1024 * 1024);
        }

        private static string Supervisor => Path.Combine(
            FindRepositoryRoot(), "Meta", "StrataLint", "scripts", "report", "report-supervisor.sh");

        private string WriteExecutable(string name, string contents)
        {
            var path = Path.Combine(Root, name);
            File.WriteAllText(path, contents + "\n", new UTF8Encoding(false));
            var chmod = BoundedProcessRunner.Run(
                "/bin/chmod", ["+x", path], Root, TimeSpan.FromSeconds(5), 4096);
            Assert.Equal(0, chmod.ExitCode);
            return path;
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
}
