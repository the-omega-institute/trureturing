using System.Diagnostics;
using System.Globalization;
using System.Text;

namespace StrataLint.ReportSupervisor.Tests;

public sealed class ReportSupervisorObservationFailureTests
{
    [Theory]
    [InlineData("members", 0)]
    [InlineData("rss", 0)]
    [InlineData("fd", 0)]
    [InlineData("markers", 0)]
    [InlineData("members", 7)]
    [InlineData("rss", 7)]
    [InlineData("fd", 7)]
    [InlineData("markers", 7)]
    public void KilledObserverPreservesCompletedWorkerExit(string operation, int workerExit)
    {
        if (operation == "markers" && Directory.Exists("/proc")) return;
        using var fixture = new ReportSupervisorFixture();
        InstallKilledObserver(fixture, operation);
        var worker = fixture.WriteExecutable("observation-worker.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' "$$" > "$1"
            while [[ ! -e "$PWD/sampling-tool-failed" ]]; do :; done
            printf 'completed\n' > "$PWD/worker-completed"
            exit __EXIT__
            """.Replace("__EXIT__", workerExit.ToString(CultureInfo.InvariantCulture), StringComparison.Ordinal));

        var result = fixture.Run("lean-producer", leanSlot: true, worker);

        Assert.Equal(workerExit, result.ExitCode);
        Assert.Equal("completed\n", File.ReadAllText(Path.Combine(fixture.Root, "worker-completed")));
        AssertIncompleteObservation(Encoding.UTF8.GetString(result.StandardError));
        AssertSlotReleased(fixture);
    }

    [Theory]
    [InlineData("members")]
    [InlineData("rss")]
    [InlineData("fd")]
    [InlineData("markers")]
    public void KilledObserverPreservesTimeoutAndReapsWorkerTree(string operation)
    {
        if (operation == "markers" && Directory.Exists("/proc")) return;
        using var fixture = new ReportSupervisorFixture();
        InstallKilledObserver(fixture, operation);

        var result = fixture.RunWithEnvironment(
            "lean-producer", true, fixture.LongRunningWorker,
            fixture.ClockEnvironment,
            "STRATALINT_TEST_CLOCK_GATE_FILE=" + FailureMarker(fixture),
            "STRATALINT_BUILD_TIMEOUT_SECONDS=2");

        Assert.Equal(124, result.ExitCode);
        AssertIncompleteObservation(Encoding.UTF8.GetString(result.StandardError));
        AssertWorkerExited(fixture, fixture.ScratchRecord);
        AssertSlotReleased(fixture);
    }

    [Fact]
    public void KilledObserverPreservesCancellationAndReapsWorkerTree()
    {
        using var fixture = new ReportSupervisorFixture();
        InstallKilledObserver(fixture, "members");
        using var process = fixture.StartLongRunningProducer();
        using var watchdog = new ReportSupervisorTestWatchdog(fixture.SafetyTimeout);
        var stderr = new StringBuilder();
        process.ErrorDataReceived += (_, e) => { if (e.Data is not null) stderr.AppendLine(e.Data); };
        watchdog.Track(process);
        try
        {
            fixture.WaitUntil(
                () => File.Exists(FailureMarker(fixture)) && File.Exists(fixture.GrandchildPid)
                    && new FileInfo(fixture.GrandchildPid).Length > 0,
                "worker and observer failure did not become ready");
            var signal = fixture.RunExternalProcess(
                "/bin/kill", ["-TERM", process.Id.ToString(CultureInfo.InvariantCulture)]);
            Assert.Equal(0, signal.ExitCode);
            fixture.WaitForExit(process, "cancelled supervisor did not exit");

            process.WaitForExit();
            Assert.Equal(143, process.ExitCode);
            AssertIncompleteObservation(stderr.ToString());
            AssertWorkerExited(fixture, fixture.GrandchildPid);
            AssertSlotReleased(fixture);
        }
        finally
        {
            if (!process.HasExited) process.Kill(entireProcessTree: true);
        }
    }

    [Fact]
    public void ProcessCollectionStopsWhenItsOutputCannotBeWritten()
    {
        using var fixture = new ReportSupervisorFixture();
        var supervisor = File.ReadAllText(fixture.Supervisor);
        var start = supervisor.IndexOf("collect_process_tree() {", StringComparison.Ordinal);
        var end = supervisor.IndexOf("marker_processes() {", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        var harness = """
            set -euo pipefail
            pgrep() { : > "$PWD/discovery-continued"; }
            """ + "\n" + supervisor[start..end] + "\n" + """
            if collect_process_tree 2147481000 >&-; then exit 0; else exit "$?"; fi
            """;

        var result = fixture.RunExternalProcess("/bin/bash", ["-c", harness]);

        Assert.NotEqual(0, result.ExitCode);
        Assert.False(File.Exists(Path.Combine(fixture.Root, "discovery-continued")));
        Assert.Contains("printf", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
    }

    [Fact]
    public void CandidateWriteFailureIsNotMaskedByALaterVanishedProcess()
    {
        using var fixture = new ReportSupervisorFixture();
        var supervisor = File.ReadAllText(fixture.Supervisor);
        var start = supervisor.IndexOf("remember_process_candidate() {", StringComparison.Ordinal);
        var end = supervisor.IndexOf("record_supervised_processes() {", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        var harness = """
            set -euo pipefail
            PROCESS_CANDIDATES_FILE="$PWD/missing/process-candidates"
            process_start_identity() {
              [[ "$1" == 2147481000 ]] || return 1
              printf 'start-id\n'
            }
            """ + "\n" + supervisor[start..end] + "\n" + """
            printf '2147481000\n2147481001\n' | record_process_candidates
            printf 'continued\n'
            """;

        var result = fixture.RunExternalProcess("/bin/bash", ["-c", harness]);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains("process-candidates", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
    }

    private static string FailureMarker(ReportSupervisorFixture fixture) =>
        Path.Combine(fixture.Root, "sampling-tool-failed");

    private static void InstallKilledObserver(ReportSupervisorFixture fixture, string operation)
    {
        _ = fixture.WriteExecutable("sort", """
            #!/usr/bin/env bash
            set -euo pipefail
            if [[ "__OPERATION__" == members && "$*" == -un \
              && ( -s "$PWD/scratch.txt" || -s "$PWD/grandchild.pid" ) ]]; then
              printf 'failed\n' > "$PWD/sampling-tool-failed"
              kill -KILL "$$"
            fi
            exec /usr/bin/sort "$@"
            """.Replace("__OPERATION__", operation, StringComparison.Ordinal));
        _ = fixture.WriteExecutable("awk", """
            #!/usr/bin/env bash
            set -euo pipefail
            matched=0
            case "__OPERATION__:$*" in
              rss:*'sum + 0'*|fd:*'NR + 0'*|fd:*'count + 0'*|markers:*'marker='*) matched=1 ;;
            esac
            if [[ "$matched" == 1 \
              && ( -s "$PWD/scratch.txt" || -s "$PWD/grandchild.pid" ) ]]; then
              printf 'failed\n' > "$PWD/sampling-tool-failed"
              kill -KILL "$$"
            fi
            exec /usr/bin/awk "$@"
            """.Replace("__OPERATION__", operation, StringComparison.Ordinal));
    }

    private static void AssertIncompleteObservation(string stderr)
    {
        Assert.Contains("RESOURCE_OBSERVATION_UNAVAILABLE stage=report-supervisor-lean-producer", stderr, StringComparison.Ordinal);
        Assert.Contains("exit=137", stderr, StringComparison.Ordinal);
        Assert.Contains("fd_peak=unknown rss_peak_kb=unknown", stderr, StringComparison.Ordinal);
    }

    private static void AssertSlotReleased(ReportSupervisorFixture fixture) =>
        Assert.Empty(Directory.GetDirectories(Path.Combine(fixture.StateRoot, "slots"), "slot-*.lock"));

    private static void AssertWorkerExited(ReportSupervisorFixture fixture, string pidFile)
    {
        var pid = int.Parse(File.ReadAllText(pidFile).Trim(), CultureInfo.InvariantCulture);
        fixture.WaitUntil(() => !ProcessExists(pid), "worker descendant survived cleanup");
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
