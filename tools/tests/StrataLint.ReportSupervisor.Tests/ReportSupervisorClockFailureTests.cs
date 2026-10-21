using System.Diagnostics;
using System.Globalization;
using System.Text;

namespace StrataLint.ReportSupervisor.Tests;

public sealed class ReportSupervisorClockFailureTests
{
    [Theory]
    [InlineData(false, "2000000000", 7)]
    [InlineData(true, "2000000000", 7)]
    [InlineData(true, "invalid-epoch", 0)]
    [InlineData(true, "", 0)]
    public void FailedClockDoesNotBecomeAStartTime(bool injected, string output, int clockExit)
    {
        using var fixture = new ReportSupervisorFixture();
        var clock = InstallClock(fixture, 1, output, clockExit, name: injected ? "fault-clock.sh" : "date");

        var result = fixture.RunWithEnvironment("lean-producer", false, fixture.ScratchWriter,
            "STRATALINT_SUPERVISOR_CLOCK=" + (injected ? clock : string.Empty));

        Assert.Equal(2, result.ExitCode);
        AssertClockDiagnostic(result.StandardError, clockExit);
        Assert.False(File.Exists(fixture.ScratchRecord));
        AssertRunReleased(fixture);
    }

    [Theory]
    [InlineData(false, 2)] // Relative deadline initialization.
    [InlineData(true, 3)] // Millisecond start time after acquiring the slot.
    [InlineData(true, 4)] // Relative deadline initialization with an owned slot.
    public void StartupClockFailureReleasesAnyAcquiredSlot(bool leanSlot, int failedRead)
    {
        using var fixture = new ReportSupervisorFixture();
        var clock = InstallClock(fixture, failedRead, "invalid-epoch", 0);

        var result = fixture.RunWithEnvironment("lean-producer", leanSlot, fixture.ScratchWriter,
            "STRATALINT_SUPERVISOR_CLOCK=" + clock);

        Assert.Equal(2, result.ExitCode);
        AssertClockDiagnostic(result.StandardError, 0);
        Assert.False(File.Exists(fixture.ScratchRecord));
        AssertRunReleased(fixture);
    }

    [Theory]
    [InlineData(1, false)] // Slot acquisition deadline.
    [InlineData(2, false)] // Claim guard deadline, inside a conditional call.
    [InlineData(3, true)] // Reclaim guard deadline, after ordinary contention.
    [InlineData(4, true)] // Ownerless lock initialization grace.
    [InlineData(5, true)] // Slot wait deadline comparison.
    public void LockClockFailureDoesNotBecomeContentionOrStaleness(int failedRead, bool occupied)
    {
        using var fixture = new ReportSupervisorFixture();
        var slot = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        if (occupied)
        {
            Directory.CreateDirectory(slot);
            Directory.SetLastWriteTimeUtc(slot, new DateTime(2100, 1, 1, 0, 0, 0, DateTimeKind.Utc));
        }
        var clock = InstallClock(fixture, failedRead, "invalid-epoch", 0);

        var result = fixture.RunWithEnvironment("lean-producer", true, fixture.ScratchWriter,
            "STRATALINT_SUPERVISOR_CLOCK=" + clock, "STRATALINT_LEAN_MAX_CONCURRENCY=1");

        Assert.Equal(2, result.ExitCode);
        AssertClockDiagnostic(result.StandardError, 0);
        Assert.False(File.Exists(fixture.ScratchRecord));
        Assert.Empty(Directory.GetDirectories(Path.Combine(fixture.StateRoot, "runs")));
        Assert.Equal(occupied ? [slot] : Array.Empty<string>(),
            Directory.GetDirectories(Path.Combine(fixture.StateRoot, "slots")));
    }

    [Fact]
    public void GuardReclamationClockFailurePreservesTheUnconfirmedLock()
    {
        using var fixture = new ReportSupervisorFixture();
        var guard = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock.reclaim-guard");
        Directory.CreateDirectory(guard);
        Directory.SetLastWriteTimeUtc(guard, new DateTime(2100, 1, 1, 0, 0, 0, DateTimeKind.Utc));
        var clock = InstallClock(fixture, 3, "invalid-epoch", 0);

        var result = fixture.RunWithEnvironment("lean-producer", true, fixture.ScratchWriter,
            "STRATALINT_SUPERVISOR_CLOCK=" + clock, "STRATALINT_LEAN_MAX_CONCURRENCY=1");

        Assert.Equal(2, result.ExitCode);
        AssertClockDiagnostic(result.StandardError, 0);
        Assert.False(File.Exists(fixture.ScratchRecord));
        Assert.Empty(Directory.GetDirectories(Path.Combine(fixture.StateRoot, "runs")));
        Assert.Equal([guard], Directory.GetDirectories(Path.Combine(fixture.StateRoot, "slots")));
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    public void RelayClockFailureStillTerminatesAndReapsTheOwnedRelay(int failedRead)
    {
        using var fixture = new ReportSupervisorFixture();
        var clock = InstallClock(fixture, failedRead, "invalid-epoch", 0);
        var supervisor = File.ReadAllText(fixture.Supervisor);
        var clockStart = supervisor.IndexOf("now_seconds() {", StringComparison.Ordinal);
        var clockEnd = supervisor.IndexOf("lock_mtime() {", clockStart, StringComparison.Ordinal);
        var relayStart = supervisor.IndexOf("wait_for_relay() {", StringComparison.Ordinal);
        var relayEnd = supervisor.IndexOf("finish() {", relayStart, StringComparison.Ordinal);
        Assert.True(clockStart >= 0 && clockEnd > clockStart && relayStart >= 0 && relayEnd > relayStart);
        var harness = "set -euo pipefail\nCLOCK_SOURCE=\"" + clock + "\"\n"
            + supervisor[clockStart..clockEnd] + "\n" + supervisor[relayStart..relayEnd] + "\n" + """
            mkfifo "$PWD/relay-hold.fifo"
            { IFS= read -r _ < "$PWD/relay-hold.fifo"; } &
            relay=$!
            trap 'kill -KILL "$relay" 2>/dev/null || true; wait "$relay" 2>/dev/null || true' EXIT
            rc=0
            wait_for_relay "$relay" || rc=$?
            if kill -0 "$relay" 2>/dev/null; then exit 99; fi
            printf 'reaped\n'
            exit "$rc"
            """;

        var result = fixture.RunExternalProcess("/bin/bash", ["-c", harness]);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("reaped\n", Encoding.UTF8.GetString(result.StandardOutput));
        AssertClockDiagnostic(result.StandardError, 0);
    }

    [Fact]
    public void InvalidThirdReadCannotPassTheInitialOuterDeadlineCheck()
    {
        using var fixture = new ReportSupervisorFixture();
        var clock = InstallClock(fixture, 3, "invalid-epoch", 0);

        var result = fixture.RunWithEnvironment("ci-bootstrap", false, fixture.ScratchWriter,
            "STRATALINT_SUPERVISOR_CLOCK=" + clock, "PREFLIGHT_DEADLINE_AT=2000000060");

        Assert.Equal(2, result.ExitCode);
        AssertClockDiagnostic(result.StandardError, 0);
        Assert.False(File.Exists(fixture.ScratchRecord));
        AssertRunReleased(fixture);
    }

    [Theory]
    [InlineData(false, false, 4, "invalid-epoch", 0)]
    [InlineData(false, true, 5, "invalid-epoch", 0)]
    [InlineData(true, false, 6, "invalid-epoch", 0)]
    [InlineData(true, false, 8, "invalid-epoch", 0)]
    [InlineData(true, false, 6, "2000000000", 7)]
    public void RunningDeadlineClockFailureFailsAndReapsOwnedProcesses(
        bool leanSlot, bool outerDeadline, int failedRead, string output, int clockExit)
    {
        // On hosts without /proc, marker observation consumes the intervening
        // clock reads. Linux goes directly to the authoritative deadline read.
        if (Directory.Exists("/proc")) failedRead = leanSlot ? 5 : outerDeadline ? 4 : 3;
        using var fixture = new ReportSupervisorFixture();
        var clock = InstallClock(fixture, failedRead, output, clockExit, waitForWorker: true);
        var worker = InstallCompletingWorker(fixture, 0);

        var result = fixture.RunWithEnvironment("lean-producer", leanSlot, worker,
            "STRATALINT_SUPERVISOR_CLOCK=" + clock,
            "PREFLIGHT_DEADLINE_AT=" + (outerDeadline ? "2000000060" : string.Empty));

        Assert.Equal(2, result.ExitCode);
        AssertClockDiagnostic(result.StandardError, clockExit);
        AssertWorkerExited(fixture, fixture.ScratchRecord);
        AssertWorkerExited(fixture, Path.Combine(fixture.Root, "clock-worker.pid"));
        AssertRunReleased(fixture);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(7)]
    public void ObservationOnlyClockFailurePreservesCollectedWorkerOutcome(int workerExit)
    {
        if (Directory.Exists("/proc")) return;
        using var fixture = new ReportSupervisorFixture();
        var clock = InstallClock(fixture, 3, "invalid-epoch", 0, waitForWorker: true);
        var worker = InstallCompletingWorker(fixture, workerExit);

        var result = fixture.RunWithEnvironment("lean-producer", false, worker,
            "STRATALINT_SUPERVISOR_CLOCK=" + clock);

        Assert.Equal(workerExit, result.ExitCode);
        AssertClockDiagnostic(result.StandardError, 0);
        var stderr = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("RESOURCE_OBSERVATION_UNAVAILABLE", stderr, StringComparison.Ordinal);
        Assert.Contains("fd_peak=unknown rss_peak_kb=unknown", stderr, StringComparison.Ordinal);
        AssertWorkerExited(fixture, fixture.ScratchRecord);
        AssertRunReleased(fixture);
    }

    [Fact]
    public void PersistentClockFailureReapsAMarkerOnlyDoubleForkedSession()
    {
        if (Directory.Exists("/proc")) return;
        using var fixture = new ReportSupervisorFixture();
        // The fixture's synthetic pgrep reports scratch.txt regardless of its
        // actual parent. This case needs native ancestry and marker discovery.
        File.Delete(Path.Combine(fixture.Root, "ps"));
        File.Delete(Path.Combine(fixture.Root, "pgrep"));
        _ = fixture.WriteExecutable("cat", """
            #!/usr/bin/env bash
            printf '%s\n' "$$" >> "$PWD/relay.pids"
            exec /bin/cat "$@"
            """);
        var clock = fixture.WriteExecutable("persistent-clock.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            current=0
            [[ ! -f "$PWD/persistent-clock.count" ]] || read -r current < "$PWD/persistent-clock.count"
            current=$((current + 1))
            printf '%s\n' "$current" > "$PWD/persistent-clock.count"
            if (( current >= 5 )); then
              if (( current == 5 )); then
                while [[ ! -s "$PWD/scratch.txt" || ! -s "$PWD/orphan-ready" ]]; do :; done
                read -r orphan < "$PWD/scratch.txt"
                read -r ready < "$PWD/orphan-ready"
                [[ "$ready" == "$orphan" ]]
                while [[ "$(ps -o ppid= -p "$orphan" | tr -d ' ')" != 1 ]]; do :; done
                ps -o pid=,ppid=,pgid= -p "$orphan" > "$PWD/orphan-topology"
                lsof -a -p "$orphan" -d 1,2,9 > "$PWD/orphan-fds"
                for run in "$STRATALINT_SUPERVISOR_ROOT"/runs/run.*; do
                  cp "$run/process-candidates" "$PWD/candidates-before-fault"
                  printf '%s/process.marker\n' "$(cd "$run" && pwd -P)" > "$PWD/orphan-marker"
                done
              fi
              printf '%s\n' "$current" >> "$PWD/failed-clock-reads"
              printf '2000000000\n'
              exit 7
            fi
            printf '2000000000\n'
            """);
        var worker = fixture.WriteExecutable("persistent-clock-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' "$$" > "$PWD/clock-worker.pid"
            "__DOUBLE_FORK__" "$1" "$PWD/orphan-ready"
            mkfifo "$PWD/worker-hold.fifo"
            IFS= read -r _ < "$PWD/worker-hold.fifo"
            """.Replace("__DOUBLE_FORK__", fixture.DoubleForkWorker, StringComparison.Ordinal));
        using var unrelated = fixture.StartSentinelBlockedProcess();
        try
        {
            var result = fixture.RunWithEnvironment("lean-producer", true, worker,
                "STRATALINT_SUPERVISOR_CLOCK=" + clock);

            Assert.Equal(2, result.ExitCode);
            AssertClockDiagnostic(result.StandardError, 7);
            var stderr = Encoding.UTF8.GetString(result.StandardError);
            Assert.Contains("RESOURCE_OBSERVATION_UNAVAILABLE", stderr, StringComparison.Ordinal);
            Assert.Contains("fd_peak=unknown rss_peak_kb=unknown", stderr, StringComparison.Ordinal);
            var topology = File.ReadAllText(Path.Combine(fixture.Root, "orphan-topology"))
                .Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries);
            Assert.Equal("1", topology[1]);
            Assert.NotEqual(File.ReadAllText(Path.Combine(fixture.Root, "clock-worker.pid")).Trim(), topology[2]);
            Assert.Equal(File.ReadAllText(fixture.ScratchRecord).Trim(), topology[0]);
            Assert.Equal(File.ReadAllText(Path.Combine(fixture.Root, "orphan-ready")).Trim(), topology[0]);
            Assert.Empty(File.ReadAllText(Path.Combine(fixture.Root, "candidates-before-fault")));
            var marker = File.ReadAllText(Path.Combine(fixture.Root, "orphan-marker")).Trim();
            var fds = File.ReadAllLines(Path.Combine(fixture.Root, "orphan-fds"))
                .Skip(1).Select(line => line.Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries)).ToArray();
            Assert.Contains(fds, fields => fields[3] == "9r" && fields[^1] == marker);
            Assert.All(fds.Where(fields => fields[3] is "1w" or "2w"),
                fields => Assert.Equal("/dev/null", fields[^1]));
            var failedReads = File.ReadAllLines(Path.Combine(fixture.Root, "failed-clock-reads"))
                .Select(value => int.Parse(value, CultureInfo.InvariantCulture)).ToArray();
            Assert.Equal(Enumerable.Range(5, int.Parse(
                File.ReadAllText(Path.Combine(fixture.Root, "persistent-clock.count")).Trim(),
                CultureInfo.InvariantCulture) - 4), failedReads);
            AssertWorkerExited(fixture, fixture.ScratchRecord);
            AssertWorkerExited(fixture, Path.Combine(fixture.Root, "clock-worker.pid"));
            var relays = File.ReadAllLines(Path.Combine(fixture.Root, "relay.pids"))
                .Select(value => int.Parse(value, CultureInfo.InvariantCulture)).ToArray();
            Assert.Equal(2, relays.Length);
            Assert.All(relays, pid => Assert.False(ProcessExists(pid), "owned relay was not reaped"));
            AssertRunReleased(fixture);
            Assert.False(unrelated.HasExited);
        }
        finally
        {
            // A failing regression must not leave its marker-only orphan behind.
            foreach (var pidFile in new[] { fixture.ScratchRecord, Path.Combine(fixture.Root, "clock-worker.pid") })
            {
                if (!File.Exists(pidFile)) continue;
                var pid = int.Parse(File.ReadAllText(pidFile).Trim(), CultureInfo.InvariantCulture);
                if (ProcessExists(pid))
                    _ = fixture.RunExternalProcess("/bin/kill", ["-KILL", pid.ToString(CultureInfo.InvariantCulture)]);
            }
            if (!unrelated.HasExited) unrelated.Kill();
            unrelated.WaitForExit();
        }
    }

    private static string InstallClock(
        ReportSupervisorFixture fixture, int failedRead, string output, int clockExit,
        bool waitForWorker = false, string name = "fault-clock.sh") =>
        fixture.WriteExecutable(name, """
            #!/usr/bin/env bash
            set -euo pipefail
            current=0
            if [[ -f "$PWD/fault-clock.count" ]]; then read -r current < "$PWD/fault-clock.count"; fi
            current=$((current + 1))
            printf '%s\n' "$current" > "$PWD/fault-clock.count"
            if [[ "$current" == __READ__ ]]; then
              if [[ __WAIT__ == 1 ]]; then
                while [[ ! -s "$PWD/scratch.txt" ]]; do :; done
              fi
              printf 'failed\n' > "$PWD/clock-failed"
              printf '%s\n' '__OUTPUT__'
              exit __EXIT__
            fi
            printf '2000000000\n'
            """
            .Replace("__READ__", failedRead.ToString(CultureInfo.InvariantCulture), StringComparison.Ordinal)
            .Replace("__WAIT__", waitForWorker ? "1" : "0", StringComparison.Ordinal)
            .Replace("__OUTPUT__", output, StringComparison.Ordinal)
            .Replace("__EXIT__", clockExit.ToString(CultureInfo.InvariantCulture), StringComparison.Ordinal));

    private static string InstallCompletingWorker(ReportSupervisorFixture fixture, int workerExit) =>
        fixture.WriteExecutable("clock-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' "$$" > "$PWD/clock-worker.pid"
            mkfifo "$PWD/clock-child-release.fifo"
            { IFS= read -r _ < "$PWD/clock-child-release.fifo"; } &
            printf '%s\n' "$!" > "$1"
            while [[ ! -s "$PWD/clock-failed" ]]; do :; done
            exit __EXIT__
            """.Replace("__EXIT__", workerExit.ToString(CultureInfo.InvariantCulture), StringComparison.Ordinal));

    private static void AssertClockDiagnostic(byte[] standardError, int clockExit)
    {
        var stderr = Encoding.UTF8.GetString(standardError);
        Assert.Contains(clockExit == 0 ? "clock source returned a non-integer epoch" : "clock command failed exit=7",
            stderr, StringComparison.Ordinal);
        Assert.DoesNotContain("syntax error", stderr, StringComparison.Ordinal);
    }

    private static void AssertRunReleased(ReportSupervisorFixture fixture)
    {
        Assert.Empty(Directory.GetDirectories(Path.Combine(fixture.StateRoot, "runs")));
        Assert.Empty(Directory.GetDirectories(Path.Combine(fixture.StateRoot, "slots")));
    }

    private static void AssertWorkerExited(ReportSupervisorFixture fixture, string pidFile)
    {
        var pid = int.Parse(File.ReadAllText(pidFile).Trim(), CultureInfo.InvariantCulture);
        fixture.WaitUntil(() => !ProcessExists(pid), "clock failure left an owned process alive");
    }

    private static bool ProcessExists(int pid)
    {
        try
        {
            using var process = Process.GetProcessById(pid);
            return !process.HasExited;
        }
        catch (ArgumentException)
        {
            return false;
        }
    }
}
