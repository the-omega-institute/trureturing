using System.Diagnostics;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReportSupervisorScriptTests
{
    [Fact]
    public void ExpiredLeaseOwnedByALiveProcessIsReclaimed()
    {
        using var fixture = new LeaseWatchdogFixture();
        fixture.CreateTimestampedSlotOwnedByCurrentProcess(
            DateTimeOffset.UtcNow.AddMinutes(-1).ToUnixTimeMilliseconds());

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LEAN_SLOT_LEASE_SECONDS=5",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=3");

        Assert.Equal(0, result.ExitCode);
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
            _ = WriteExecutable("ps", """
                #!/usr/bin/env bash
                if [[ "${STRATALINT_TEST_PS_FAIL_ALL:-}" == "1" ]]; then exit 1; fi
                previous=""
                for argument in "$@"; do
                  if [[ "$previous" == "-p" && "$argument" == "${STRATALINT_TEST_PS_FAIL_PID:-}" ]]; then
                    exit 1
                  fi
                  previous="$argument"
                done
                exec /bin/ps "$@"
                """);
        }

        internal string Root => temporary.Path;
        internal string StateRoot => Path.Combine(Root, "state");
        internal string MetricsLog => Path.Combine(Root, "metrics.jsonl");
        internal string Slot => Path.Combine(StateRoot, "slots", "slot-1.lock");
        internal string ProgressLogRoot => Path.Combine(Root, "producer.logs");
        internal string SleepWorkerPidFile => Path.Combine(Root, "sleep-worker.pid");
        internal string SuccessWorker { get; }
        internal string SleepWorker { get; }
        internal string OleanProgressWorker { get; }
        internal string PipeProgressWorker { get; }
        internal string LogProgressWorker { get; }

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
