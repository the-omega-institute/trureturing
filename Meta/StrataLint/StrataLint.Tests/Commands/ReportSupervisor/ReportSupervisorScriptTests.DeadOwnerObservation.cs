using System.Diagnostics;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReportSupervisorScriptTests
{
    [Theory]
    [InlineData("4242 (worker) S 1 4242", true)]
    [InlineData("4242 (worker with ) paren) Z 1 4242", false)]
    [InlineData("4242 (dead) X 1 4242", false)]
    public void LinuxProcStatDistinguishesRunningAndDeadStates(string stat, bool expected)
    {
        Assert.Equal(expected, ProcStatRepresentsRunning(stat));
    }

    [Theory]
    [InlineData('S', 0)]
    [InlineData('Z', 1)]
    [InlineData('X', 1)]
    public void KillZeroIsQualifiedByLinuxProcState(char state, int expectedExit)
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachSyntheticProcStat(Environment.ProcessId, state);

        var result = fixture.RunProcessExists(Environment.ProcessId);

        Assert.Equal(expectedExit, result.ExitCode);
    }

    [Fact]
    public void OldEpochOnLiveCanonicalOwnerDoesNotPermitReclaim()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.CreateTimestampedSlotOwnedByCurrentProcess(
            DateTimeOffset.UtcNow.AddMinutes(-1).ToUnixTimeMilliseconds());

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=3");

        Assert.Equal(2, result.ExitCode);
        Assert.True(fixture.SlotExists());
    }

    [Fact]
    public void UnreadableLiveOwnerIdentityIsNotGuessedStale()
    {
        using var fixture = new DeadOwnerObservationFixture();
        var slot = fixture.CreateSlotOwnedByCurrentProcess();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.ClockBin}:{fixture.Root}:{fixture.HostPath}",
            $"STRATALINT_TEST_PS_FAIL_PID={Environment.ProcessId}",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(Directory.Exists(slot));
    }

    [Fact]
    public void ClaimantRecordsUnknownStartWithEpochWhenStartIdentityIsUnreadable()
    {
        using var fixture = new DeadOwnerObservationFixture();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.Root}:{fixture.HostPath}",
            "STRATALINT_TEST_PS_FAIL_ALL=1",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void OwnerRecordContainsPidStartAndEpoch()
    {
        using var fixture = new DeadOwnerObservationFixture();
        using var holder = fixture.Start(
            fixture.SleepWorker,
            fixture.SyntheticProcessEnvironment(fixture.SleepWorkerPidFile, 3));
        Assert.True(SpinWait.SpinUntil(
            () => fixture.SlotExists() && File.Exists(fixture.SleepWorkerPidFile),
            TimeSpan.FromSeconds(10)));
        var owner = File.ReadAllText(Path.Combine(fixture.Slot, "owner")).Trim().Split('|');

        Assert.Equal(3, owner.Length);
        Assert.Equal(
            holder.Id.ToString(System.Globalization.CultureInfo.InvariantCulture),
            owner[0]);
        Assert.False(string.IsNullOrWhiteSpace(owner[1]));
        Assert.True(long.Parse(owner[2], System.Globalization.CultureInfo.InvariantCulture) > 1_000_000_000_000);
    }

    [Fact]
    public void DeadOwnerFromMetadataCrashWindowIsReclaimed()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.CreateSlotWithOwner("99999999|definitely-dead|0\n");

        Assert.False(File.Exists(Path.Combine(fixture.Slot, "marker")));
        Assert.False(File.Exists(Path.Combine(fixture.Slot, "group")));

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=3");

        Assert.True(
            result.ExitCode == 0,
            $"stdout: {Encoding.UTF8.GetString(result.StandardOutput)}\n"
            + $"stderr: {Encoding.UTF8.GetString(result.StandardError)}");
    }

    [Fact]
    public void SigkillOrphanKeepsSlotUntilTheWholeProcessGroupIsDead()
    {
        using var fixture = new DeadOwnerObservationFixture();
        using var holder = fixture.Start(fixture.SleepWorker);
        Assert.True(SpinWait.SpinUntil(
            () => fixture.SlotMetadataIsPublished()
                && File.Exists(fixture.SleepWorkerPidFile),
            TimeSpan.FromSeconds(10)));
        var orphanPid = fixture.ReadSleepWorkerPid();
        var group = fixture.ReadProcessGroup();
        Assert.Equal(orphanPid, group.GroupId);
        Assert.Equal(orphanPid, group.LeaderPid);

        var signal = BoundedProcessRunner.Run(
            "/bin/kill",
            ["-KILL", holder.Id.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            fixture.Root,
            TimeSpan.FromSeconds(5),
            4096);
        Assert.Equal(0, signal.ExitCode);
        Assert.True(holder.WaitForExit(5_000));
        Assert.True(ProcessExists(orphanPid));

        var blocked = fixture.Run(
            fixture.SuccessWorker,
            fixture.SyntheticProcessEnvironment(fixture.SleepWorkerPidFile, 1));

        Assert.Equal(2, blocked.ExitCode);
        Assert.True(fixture.SlotExists());
        Assert.True(ProcessExists(orphanPid));
        fixture.KillProcess(orphanPid);
        Assert.True(SpinWait.SpinUntil(
            () => !ProcessExists(orphanPid),
            TimeSpan.FromSeconds(5)));

        var reclaimed = fixture.Run(
            fixture.SuccessWorker,
            fixture.SyntheticProcessEnvironment(fixture.SleepWorkerPidFile, 3));

        Assert.Equal(0, reclaimed.ExitCode);
    }

    [Fact]
    public void LiveClosedFdDescendantPreventsReclaimWithoutBeingKilled()
    {
        using var fixture = new DeadOwnerObservationFixture();
        using var holder = fixture.Start(
            fixture.ClosedFdDescendantWorker,
            fixture.SyntheticProcessEnvironment(fixture.ClosedFdDescendantPidFile, 3));
        Assert.True(SpinWait.SpinUntil(
            () => fixture.SlotExists()
                && fixture.SlotMetadataIsPublished()
                && File.Exists(fixture.ClosedFdLeaderPidFile)
                && File.Exists(fixture.ClosedFdDescendantPidFile),
            TimeSpan.FromSeconds(10)));
        var leaderPid = fixture.ReadPid(fixture.ClosedFdLeaderPidFile);
        var descendantPid = fixture.ReadPid(fixture.ClosedFdDescendantPidFile);
        var group = fixture.ReadProcessGroup();
        Assert.Equal(leaderPid, group.GroupId);
        Assert.Equal(leaderPid, group.LeaderPid);
        Assert.True(File.Exists(Path.Combine(fixture.Slot, "marker")));
        Assert.True(File.Exists(Path.Combine(fixture.Slot, "group")));

        fixture.KillProcess(holder.Id);
        fixture.KillProcess(leaderPid);
        Assert.True(holder.WaitForExit(5_000));
        Assert.True(ProcessExists(descendantPid));

        var blocked = fixture.Run(
            fixture.SuccessWorker,
            fixture.SyntheticProcessEnvironment(fixture.ClosedFdDescendantPidFile, 1));

        Assert.Equal(2, blocked.ExitCode);
        Assert.True(fixture.SlotExists());
        Assert.True(ProcessExists(descendantPid));
        File.Delete(fixture.ClosedFdDescendantHoldFile);
        Assert.True(SpinWait.SpinUntil(
            () => !ProcessExists(descendantPid),
            TimeSpan.FromSeconds(10)));

        var reclaimed = fixture.Run(
            fixture.SuccessWorker,
            fixture.SyntheticProcessEnvironment(fixture.ClosedFdDescendantPidFile, 3));

        Assert.Equal(0, reclaimed.ExitCode);
    }

    [Fact]
    public void MalformedNonemptyOwnerFailsClosed()
    {
        using var fixture = new DeadOwnerObservationFixture();
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
        using var fixture = new DeadOwnerObservationFixture();
        fixture.CreateSlotWithOwner(
            $"{Environment.ProcessId}|unknown|{DateTimeOffset.UtcNow.AddMinutes(-1).ToUnixTimeMilliseconds()}\n");

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(fixture.SlotExists());
    }

    [Fact]
    public void ThreeFieldOwnerWhosePidWasReusedIsReclaimed()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.CreateSlotWithOwner(
            $"{Environment.ProcessId}|not-the-current-start|{DateTimeOffset.UtcNow.ToUnixTimeMilliseconds()}\n");
        fixture.AttachEmptyProcessGroup();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.Root}:{fixture.HostPath}",
            $"STRATALINT_TEST_PS_REUSED_PID={Environment.ProcessId}",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=5");

        Assert.True(
            result.ExitCode == 0,
            $"stdout: {Encoding.UTF8.GetString(result.StandardOutput)}\n"
            + $"stderr: {Encoding.UTF8.GetString(result.StandardError)}");
    }

    [Fact]
    public void MalformedSuccessfulProcessTableFailsClosed()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.CreateSlotWithOwner("99999999|definitely-dead|0\n");
        _ = fixture.AttachEmptyProcessGroup();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.Root}:{fixture.HostPath}",
            "STRATALINT_TEST_PS_MALFORMED_TABLE=1",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(fixture.SlotExists());
    }

    [Fact]
    public void ProcMarkerScanConsidersEveryOpenDescriptor()
    {
        using var fixture = new DeadOwnerObservationFixture();
        var marker = Path.Combine(fixture.Root, "synthetic-process.marker");
        File.WriteAllText(marker, string.Empty, new UTF8Encoding(false));
        fixture.AttachSyntheticMarkerDescriptor(Environment.ProcessId, 37, marker);

        var result = fixture.RunMarkerScan(marker);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            Environment.ProcessId.ToString(System.Globalization.CultureInfo.InvariantCulture),
            Encoding.UTF8.GetString(result.StandardOutput).Trim());
    }

    [Fact]
    public void ForeignUidProcEntryDoesNotObscureQuiescence()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachSyntheticForeignProcess();
        var marker = Path.Combine(fixture.Root, "synthetic-process.marker");
        File.WriteAllText(marker, string.Empty, new UTF8Encoding(false));

        var result = fixture.RunMarkerScan(marker);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.StandardOutput);
    }

    [Fact]
    public void ZombieOnlyProcessGroupAllowsReclaim()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.CreateSlotWithOwner("99999999|definitely-dead|0\n");
        _ = fixture.AttachEmptyProcessGroup();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.Root}:{fixture.HostPath}",
            "STRATALINT_TEST_PS_ZOMBIE_GROUP=99999999",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=3");

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
        var fence = Path.Combine(fixture.Root, "synthetic-process.marker");
        File.WriteAllText(fence, string.Empty, new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(staleSlot, "marker"),
            fence + "\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(staleSlot, "group"),
            "99999999|99999999|definitely-dead\n",
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

    private sealed class DeadOwnerObservationFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal DeadOwnerObservationFixture()
        {
            _ = WriteExecutable("restore-clock.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                /bin/ln -sf /bin/date "$1.next"
                /bin/mv -f -- "$1.next" "$1"
                """);
            SuccessWorker = WriteExecutable("success.sh", "#!/usr/bin/env bash\nexit 0");
            SleepWorker = WriteExecutable("sleep.sh", """
                #!/usr/bin/env bash
                printf '%s\n' "$$" > "$1/sleep-worker.pid"
                exec sleep 60
                """);
            OleanProgressWorker = WriteExecutable("olean-progress.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                mkdir -p "$1/.lake/build/lib/lean"
                for index in 1 2 3 4; do
                  touch "$1/.lake/build/lib/lean/progress-${index}.olean"
                  sleep 1
                done
                "$1/restore-clock.sh" "$1/clock-bin/date"
                """);
            PipeProgressWorker = WriteExecutable("pipe-progress.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                for index in 1 2 3 4; do
                  printf 'progress-%s\n' "$index"
                  sleep 1
                done
                "$1/restore-clock.sh" "$1/clock-bin/date"
                """);
            LogProgressWorker = WriteExecutable("log-progress.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                mkdir -p "$STRATALINT_LEAN_PROGRESS_LOG_ROOT"
                for index in 1 2 3 4; do
                  printf 'progress-%s\n' "$index" >> "$STRATALINT_LEAN_PROGRESS_LOG_ROOT/build.stdout.log"
                  sleep 1
                done
                "$1/restore-clock.sh" "$1/clock-bin/date"
                """);
            CpuOnlyWorker = WriteExecutable("cpu-only.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                perl -MTime::HiRes=time -e '$end = time() + 5; 1 while time() < $end'
                "$1/restore-clock.sh" "$1/clock-bin/date"
                """);
            QuantizedLowDutyWorker = WriteExecutable("quantized-low-duty.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                sleep 5
                "$1/restore-clock.sh" "$1/clock-bin/date"
                """);
            File.WriteAllText(ClosedFdDescendantHoldFile, string.Empty, new UTF8Encoding(false));
            ClosedFdDescendantWorker = WriteExecutable("closed-fd-descendant.sh", """
                #!/usr/bin/env bash
                set -euo pipefail
                printf '%s\n' "$$" > "$1/closed-fd-leader.pid"
                (
                  trap '' TERM
                  exec 9<&- >/dev/null 2>&1
                  while [[ -e "$1/closed-fd-descendant.hold" ]]; do sleep 0.05; done
                ) &
                descendant_pid=$!
                printf '%s\n' "$descendant_pid" > "$1/closed-fd-descendant.pid"
                wait "$descendant_pid"
                """);
            _ = WriteExecutable("ps", """
                #!/usr/bin/env bash
                if [[ "${STRATALINT_TEST_PS_FAIL_ALL:-}" == "1" ]]; then exit 1; fi
                if [[ "${STRATALINT_TEST_PS_MALFORMED_TABLE:-}" == "1" && "$*" == *"pid=,pgid=,stat="* ]]; then
                  printf 'malformed-successful-row\n'
                  exit 0
                fi
                if [[ -n "${STRATALINT_TEST_PS_ZOMBIE_GROUP:-}" && "$*" == *"pid=,pgid=,stat="* ]]; then
                  printf '424242 %s Z+\n' "$STRATALINT_TEST_PS_ZOMBIE_GROUP"
                  exit 0
                fi
                if [[ "${STRATALINT_TEST_QUANTIZED_CPU:-}" == "1" && "$*" == *"time="* ]]; then
                  value=0
                  if [[ -f "$STRATALINT_TEST_CLOCK_FILE" ]]; then read -r value < "$STRATALINT_TEST_CLOCK_FILE"; fi
                  seconds=$((value / 60))
                  printf '%02d:%02d:%02d\n' $((seconds / 3600)) $(((seconds / 60) % 60)) $((seconds % 60))
                  exit 0
                fi
                previous=""
                requested_pid=""
                for argument in "$@"; do
                  if [[ "$previous" == "-p" ]]; then requested_pid="$argument"; fi
                  if [[ "$previous" == "-p" && "$argument" == "${STRATALINT_TEST_PS_REUSED_PID:-}" ]]; then
                    printf 'synthetic-current-start\n'
                    exit 0
                  fi
                  if [[ "$previous" == "-p" && "$argument" == "${STRATALINT_TEST_PS_FAIL_PID:-}" ]]; then
                    exit 1
                  fi
                  previous="$argument"
                done
                if [[ "${STRATALINT_TEST_SYNTHETIC_PROCESS_VIEW:-}" == "1" && "$*" == *"lstart="* ]]; then
                  printf 'synthetic-start-%s\n' "$requested_pid"
                  exit 0
                fi
                if [[ "${STRATALINT_TEST_SYNTHETIC_PROCESS_VIEW:-}" == "1" && "$*" == *"pid=,pgid=,stat="* ]]; then
                  pid=""
                  group=""
                  if [[ -s "$STRATALINT_TEST_GROUP_MEMBER_PID_FILE" ]]; then
                    read -r pid < "$STRATALINT_TEST_GROUP_MEMBER_PID_FILE"
                  fi
                  if [[ -s "$STRATALINT_TEST_GROUP_RECORD" ]]; then
                    IFS='|' read -r group _ < "$STRATALINT_TEST_GROUP_RECORD"
                  fi
                  running=0
                  if [[ "$pid" =~ ^[1-9][0-9]*$ && "$group" =~ ^[1-9][0-9]*$ ]] \
                    && kill -0 "$pid" 2>/dev/null; then
                    running=1
                    if [[ -r "/proc/$pid/stat" ]]; then
                      stat="$(< "/proc/$pid/stat")"
                      suffix="${stat##*) }"
                      state="${suffix%% *}"
                      [[ "$state" == "Z" || "$state" == "X" ]] && running=0
                    fi
                  fi
                  if [[ "$running" == "1" ]]; then
                    printf '%s %s S\n' "$pid" "$group"
                  else
                    printf '1 1 S\n'
                  fi
                  exit 0
                fi
                exec /bin/ps "$@"
                """);
            _ = WriteExecutable(Path.Combine("clock-bin", "date"), """
                #!/usr/bin/env bash
                set -euo pipefail
                if [[ "$*" != "+%s" || -z "${STRATALINT_TEST_CLOCK_FILE:-}" ]]; then
                  exec /bin/date "$@"
                fi
                value=0
                if [[ -f "$STRATALINT_TEST_CLOCK_FILE" ]]; then read -r value < "$STRATALINT_TEST_CLOCK_FILE"; fi
                value=$((value + ${STRATALINT_TEST_CLOCK_STEP_SECONDS:-1}))
                printf '%s\n' "$value" > "$STRATALINT_TEST_CLOCK_FILE"
                printf '%s\n' "$value"
                """);
        }

        internal string Root => temporary.Path;
        internal string StateRoot => Path.Combine(Root, "state");
        internal string MetricsLog => Path.Combine(Root, "metrics.jsonl");
        internal string Slot => Path.Combine(StateRoot, "slots", "slot-1.lock");
        internal string ProgressLogRoot => Path.Combine(Root, "producer.logs");
        internal string SleepWorkerPidFile => Path.Combine(Root, "sleep-worker.pid");
        internal string ClosedFdLeaderPidFile => Path.Combine(Root, "closed-fd-leader.pid");
        internal string ClosedFdDescendantPidFile => Path.Combine(Root, "closed-fd-descendant.pid");
        internal string ClosedFdDescendantHoldFile => Path.Combine(Root, "closed-fd-descendant.hold");
        internal string ObservationClockFile => Path.Combine(Root, "observation.clock");
        internal string ProcessFsRoot => Path.Combine(Root, "proc");
        internal string ClockBin => Path.Combine(Root, "clock-bin");
        internal string HostPath => Environment.GetEnvironmentVariable("PATH") ?? "/bin:/usr/bin";
        internal string SuccessWorker { get; }
        internal string SleepWorker { get; }
        internal string OleanProgressWorker { get; }
        internal string PipeProgressWorker { get; }
        internal string LogProgressWorker { get; }
        internal string CpuOnlyWorker { get; }
        internal string QuantizedLowDutyWorker { get; }
        internal string ClosedFdDescendantWorker { get; }

        internal bool SlotExists() => Directory.Exists(Slot);

        internal bool SlotMetadataIsPublished() =>
            File.Exists(Path.Combine(Slot, "marker"))
            && File.Exists(Path.Combine(Slot, "group"));

        internal int ReadSleepWorkerPid() => int.Parse(
            File.ReadAllText(SleepWorkerPidFile).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        internal int ReadPid(string path) => int.Parse(
            File.ReadAllText(path).Trim(),
            System.Globalization.CultureInfo.InvariantCulture);

        internal (int GroupId, int LeaderPid) ReadProcessGroup()
        {
            var fields = File.ReadAllText(Path.Combine(Slot, "group")).Trim().Split('|');
            Assert.Equal(3, fields.Length);
            return (
                int.Parse(fields[0], System.Globalization.CultureInfo.InvariantCulture),
                int.Parse(fields[1], System.Globalization.CultureInfo.InvariantCulture));
        }

        internal void KillProcess(int pid)
        {
            var result = BoundedProcessRunner.Run(
                "/bin/kill",
                ["-KILL", pid.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                Root,
                TimeSpan.FromSeconds(5),
                4096);
            Assert.Equal(0, result.ExitCode);
        }

        internal string CreateSlotOwnedByCurrentProcess()
        {
            Directory.CreateDirectory(Slot);
            var start = BoundedProcessRunner.Run(
                "ps",
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

        internal string AttachEmptyProcessGroup()
        {
            var marker = Path.Combine(Root, "synthetic-process.marker");
            File.WriteAllText(marker, string.Empty, new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(Slot, "marker"),
                marker + "\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(Slot, "group"),
                "99999999|99999999|definitely-dead\n",
                new UTF8Encoding(false));
            return marker;
        }

        internal void AttachSyntheticMarkerDescriptor(int pid, int descriptor, string marker)
        {
            var userId = ReadUserId();
            AttachSyntheticForeignProcess();
            var fdRoot = Path.Combine(
                ProcessFsRoot,
                pid.ToString(System.Globalization.CultureInfo.InvariantCulture),
                "fd");
            Directory.CreateDirectory(fdRoot);
            File.WriteAllText(
                Path.Combine(Directory.GetParent(fdRoot)!.FullName, "status"),
                $"Name:\ttest\nUid:\t{userId}\t{userId}\t{userId}\t{userId}\n",
                new UTF8Encoding(false));
            File.CreateSymbolicLink(
                Path.Combine(fdRoot, descriptor.ToString(
                    System.Globalization.CultureInfo.InvariantCulture)),
                marker);
        }

        internal void AttachSyntheticForeignProcess()
        {
            if (ReadUserId() == 0) return;
            var foreignRoot = Path.Combine(ProcessFsRoot, "1");
            Directory.CreateDirectory(foreignRoot);
            File.WriteAllText(
                Path.Combine(foreignRoot, "status"),
                "Name:\tinit\nUid:\t0\t0\t0\t0\n",
                new UTF8Encoding(false));
        }

        internal void AttachSyntheticProcStat(int pid, char state)
        {
            var processRoot = Path.Combine(
                ProcessFsRoot,
                pid.ToString(System.Globalization.CultureInfo.InvariantCulture));
            Directory.CreateDirectory(processRoot);
            File.WriteAllText(
                Path.Combine(processRoot, "stat"),
                $"{pid} (worker with ) paren) {state} 1 {pid} 0 0\n",
                new UTF8Encoding(false));
        }

        private int ReadUserId()
        {
            var result = BoundedProcessRunner.Run(
                "/usr/bin/id", ["-u"], Root, TimeSpan.FromSeconds(5), 4096);
            Assert.Equal(0, result.ExitCode);
            return int.Parse(
                Encoding.UTF8.GetString(result.StandardOutput).Trim(),
                System.Globalization.CultureInfo.InvariantCulture);
        }

        internal string[] AcceleratedObservationEnvironment(int stepSeconds) =>
        [
            $"PATH={ClockBin}:{HostPath}",
            $"STRATALINT_TEST_CLOCK_FILE={ObservationClockFile}",
            $"STRATALINT_TEST_CLOCK_STEP_SECONDS={stepSeconds}",
            "STRATALINT_REPORT_STALL_WINDOW_SECONDS=60",
            "STRATALINT_REPORT_STALL_WINDOW_COUNT=3",
        ];

        internal string[] SyntheticProcessEnvironment(string pidFile, int lockTimeoutSeconds) =>
        [
            $"PATH={Root}:{HostPath}",
            "STRATALINT_TEST_SYNTHETIC_PROCESS_VIEW=1",
            $"STRATALINT_TEST_GROUP_MEMBER_PID_FILE={pidFile}",
            $"STRATALINT_TEST_GROUP_RECORD={Path.Combine(Slot, "group")}",
            $"STRATALINT_LOCK_TIMEOUT_SECONDS={lockTimeoutSeconds}",
        ];

        internal ProcessOutput Run(string worker, params string[] environment) =>
            BoundedProcessRunner.Run(
                "env",
                Arguments(worker, environment),
                Root,
                TimeSpan.FromSeconds(12),
                1024 * 1024);

        internal ProcessOutput RunMarkerScan(string marker) =>
            BoundedProcessRunner.Run(
                "/bin/bash",
                [
                    "-c",
                    "set -euo pipefail; PROCESS_FS_ROOT=\"$1\"; source \"$2\"; marker_processes_for_path \"$3\"",
                    "marker-scan",
                    ProcessFsRoot,
                    ProcessControl,
                    marker,
                ],
                Root,
                TimeSpan.FromSeconds(5),
                4096);

        internal ProcessOutput RunProcessExists(int pid) =>
            BoundedProcessRunner.Run(
                "/bin/bash",
                [
                    "-c",
                    "set -euo pipefail; PROCESS_FS_ROOT=\"$1\"; source \"$2\"; process_exists \"$3\"",
                    "process-exists",
                    ProcessFsRoot,
                    ProcessControl,
                    pid.ToString(System.Globalization.CultureInfo.InvariantCulture),
                ],
                Root,
                TimeSpan.FromSeconds(5),
                4096);

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
            if (File.Exists(ClosedFdDescendantPidFile)
                && int.TryParse(File.ReadAllText(ClosedFdDescendantPidFile).Trim(), out var descendantPid))
            {
                _ = BoundedProcessRunner.Run(
                    "/bin/kill", ["-KILL", descendantPid.ToString(
                        System.Globalization.CultureInfo.InvariantCulture)],
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
                "STRATALINT_BUILD_TIMEOUT_SECONDS=0",
                "STRATALINT_REPORT_OBSERVATION_POLL_SECONDS=1",
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

        private static string ProcessControl => Path.Combine(
            FindRepositoryRoot(), "Meta", "StrataLint", "scripts", "report", "report-process-control.sh");

        private string WriteExecutable(string name, string contents)
        {
            var path = Path.Combine(Root, name);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
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
