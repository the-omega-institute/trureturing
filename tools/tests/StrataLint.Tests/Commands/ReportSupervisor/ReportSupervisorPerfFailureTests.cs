using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ReportSupervisorPerfFailureTests
{
    private const string FailurePrefix =
        "{\"event\":\"performance_event_commit\",\"status\":\"failed\",";

    [Fact]
    public void PerformanceWriterReportsInvalidConfigurationAsStructuredFailure()
    {
        using var fixture = new ReportSupervisorFixture();
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var library = Path.Combine(root, "tools", "scripts", "lib", "perf-event-lib.sh");
        var spool = Path.Combine(temporary.Path, "events.jsonl");
        File.WriteAllText(spool, "{}\n", new UTF8Encoding(false));

        var result = fixture.RunExternalProcess(
            "env",
            [
                "STRATALINT_PERF_CONFIGURATION=invalid/configuration",
                "bash", "-c", "source \"$1\"; perf_flush_events \"$2\" \"$3\" test-probe",
                "bash", library, root, spool,
            ],
            temporary.Path,
            4096);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(
            "{\"event\":\"performance_event_commit\",\"status\":\"failed\","
                + "\"source\":\"test-probe\",\"reason\":\"invalid-configuration\","
                + "\"exit_code\":1}\n",
            Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Empty(result.StandardError);
    }

    [Fact]
    public void PerformanceWriterReportsTargetResolutionFailureAsStructuredFailure()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ReportSupervisorFixture();
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var library = Path.Combine(root, "tools", "scripts", "lib", "perf-event-lib.sh");
        var missingProjectRoot = Path.Combine(temporary.Path, "missing-project");
        var spool = WriteSpool(temporary.Path);
        Directory.CreateDirectory(missingProjectRoot);

        var result = RunPerfFlush(fixture, library, missingProjectRoot, spool);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(FailureNote("target-resolution-failed", 1), StandardOutput(result));
        Assert.Empty(result.StandardError);
    }

    [Fact]
    public void PerformanceWriterReportsTargetUnavailableWithoutReleaseArtifact()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ReportSupervisorFixture();
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var library = Path.Combine(root, "tools", "scripts", "lib", "perf-event-lib.sh");
        var candidateRoot = Path.Combine(temporary.Path, "candidate");
        var projectDirectory = Path.Combine(candidateRoot, "tools", "StrataLint.Cli");
        var releaseDirectory = Path.Combine(projectDirectory, "bin", "Release");
        var spool = WriteSpool(temporary.Path);
        Directory.CreateDirectory(projectDirectory);
        File.WriteAllText(
            Path.Combine(projectDirectory, "StrataLint.Cli.csproj"),
            "<Project Sdk=\"Microsoft.NET.Sdk\">"
                + "<PropertyGroup><TargetFramework>net8.0</TargetFramework>"
                + "</PropertyGroup></Project>\n",
            new UTF8Encoding(false));
        Assert.False(Directory.Exists(releaseDirectory));

        var result = RunPerfFlush(fixture, library, candidateRoot, spool);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(FailureNote("target-unavailable", 1), StandardOutput(result));
        Assert.Empty(result.StandardError);
        Assert.False(Directory.Exists(releaseDirectory));
    }

    [Fact]
    public void AppendMetricsReportsLockUnavailableAsStructuredFailure()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ReportSupervisorFixture();
        var lockDirectory = fixture.MetricsLog + ".lock";
        Directory.CreateDirectory(lockDirectory);
        File.WriteAllText(
            Path.Combine(lockDirectory, "owner"),
            Environment.ProcessId.ToString(System.Globalization.CultureInfo.InvariantCulture) + "\n",
            new UTF8Encoding(false));

        var result = fixture.RunWithEnvironment(
            "scribe-consumer",
            leanSlot: false,
            fixture.ScratchWriter,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(FailureNote("lock-unavailable", 2), StandardOutput(result));
    }

    [Fact]
    public void AppendMetricsReportsEventTempUnavailableAsStructuredFailure()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ReportSupervisorFixture();
        InstallMktempShim(fixture, "exit 37");

        var result = fixture.Run(
            "scribe-consumer",
            leanSlot: false,
            fixture.ScratchWriter);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(FailureNote("event-temp-unavailable", 37), StandardOutput(result));
    }

    [Fact]
    public void AppendMetricsReportsEventSerializationFailureAsStructuredFailure()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ReportSupervisorFixture();
        InstallMktempShim(
            fixture,
            "event_path=\"${@: -1}\"\n"
                + "event_path=\"${event_path%XXXXXXXX}fixture-directory\"\n"
                + "mkdir \"$event_path\"\n"
                + "printf '%s\\n' \"$event_path\"");

        var result = fixture.Run(
            "scribe-consumer",
            leanSlot: false,
            fixture.ScratchWriter);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(FailureNote("event-serialization-failed", 1), StandardOutput(result));
    }

    [Fact]
    public void SupervisorPreservesWorkerStdoutAndAppendsFailureNoteOnlyAfterFailure()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ReportSupervisorFixture();
        const string workerOutput = "worker stdout byte-for-byte\nsecond line\n";
        var worker = Path.Combine(fixture.Root, "stdout-worker.sh");
        WriteExecutable(
            worker,
            "#!/usr/bin/env bash\nprintf 'worker stdout byte-for-byte\\nsecond line\\n'");

        var success = fixture.Run("scribe-consumer", leanSlot: false, worker);
        var failure = fixture.RunWithEnvironment(
            "scribe-consumer",
            leanSlot: false,
            worker,
            $"STRATALINT_REPORT_METRICS_LOG={fixture.Root}");

        Assert.Equal(0, success.ExitCode);
        Assert.Equal(Encoding.UTF8.GetBytes(workerOutput), success.StandardOutput);
        Assert.Equal(0, failure.ExitCode);
        Assert.Equal(
            Encoding.UTF8.GetBytes(workerOutput + FailureNote("append-failed", 2)),
            failure.StandardOutput);
    }

    private static string WriteSpool(string directory)
    {
        var spool = Path.Combine(directory, "events.jsonl");
        File.WriteAllText(spool, "{}\n", new UTF8Encoding(false));
        return spool;
    }

    private static ProcessOutput RunPerfFlush(
        ReportSupervisorFixture fixture,
        string library,
        string root,
        string spool) => fixture.RunExternalProcess(
            "bash",
            ["-c", "source \"$1\"; perf_flush_events \"$2\" \"$3\" test-probe",
             "bash", library, root, spool],
            maximumOutputBytes: 4096);

    private static string FailureNote(string reason, int exitCode) =>
        FailurePrefix
            + $"\"source\":\"{(reason.StartsWith("target-", StringComparison.Ordinal) ? "test-probe" : "report-supervisor")}\","
            + $"\"reason\":\"{reason}\",\"exit_code\":{exitCode}}}\n";

    private static string StandardOutput(ProcessOutput result) =>
        Encoding.UTF8.GetString(result.StandardOutput);

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void InstallMktempShim(ReportSupervisorFixture fixture, string eventCommand)
    {
        var shim = Path.Combine(fixture.Root, "mktemp");
        WriteExecutable(
            shim,
            "#!/usr/bin/env bash\n"
                + "set -euo pipefail\n"
                + "if [[ \"$*\" == *\"/event.XXXXXXXX\"* ]]; then\n"
                + eventCommand + "\n"
                + "  exit 0\n"
                + "fi\n"
                + "exec /usr/bin/mktemp \"$@\"");
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteExecutable(string path, string content)
    {
        File.WriteAllText(path, content + "\n", new UTF8Encoding(false));
        File.SetUnixFileMode(
            path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
