using System.Reflection;
using System.Diagnostics;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace StrataLint.Tests;

public sealed class ReportSupervisorTestWatchdogTests
{
    [Fact]
    public void WatchdogDefaultsToNinetySecondsAndAcceptsAPositiveOverride()
    {
        Assert.Equal(90, ReportSupervisorTestWatchdog.ParseTimeoutSeconds(null));
        Assert.Equal(17, ReportSupervisorTestWatchdog.ParseTimeoutSeconds("17"));
        Assert.Equal(90, ReportSupervisorTestWatchdog.ParseTimeoutSeconds("0"));
        Assert.Equal(90, ReportSupervisorTestWatchdog.ParseTimeoutSeconds("invalid"));
        Assert.Equal(
            ReportSupervisorTestWatchdog.ConfiguredTimeoutMilliseconds,
            new ReportFactAttribute().Timeout);
        Assert.Equal(
            ReportSupervisorTestWatchdog.ConfiguredTimeoutMilliseconds,
            new ReportTheoryAttribute().Timeout);
    }

    [Fact]
    public void DiagnosticReportIncludesBoundedStdoutAndStderrTails()
    {
        var report = ReportSupervisorTestWatchdog.FormatDiagnostics(
            "example",
            new string('o', 9000),
            new string('e', 9000));

        Assert.Contains("example", report, StringComparison.Ordinal);
        Assert.Contains("stdout tail", report, StringComparison.Ordinal);
        Assert.Contains("stderr tail", report, StringComparison.Ordinal);
        Assert.True(report.Length < 17_000, $"diagnostic report was not tail-bounded: {report.Length}");
    }

    [Fact]
    public void EveryReportSupervisorScriptCaseUsesTheIndependentWatchdog()
    {
        var methods = typeof(ReportSupervisorScriptTests)
            .GetMethods(BindingFlags.Instance | BindingFlags.Public)
            .Where(method => method.GetCustomAttributes<FactAttribute>().Any())
            .ToArray();

        Assert.NotEmpty(methods);
        Assert.All(methods, method => Assert.True(
            method.GetCustomAttribute<ReportFactAttribute>() is not null
                || method.GetCustomAttribute<ReportTheoryAttribute>() is not null,
            $"{method.Name} does not use the report-script watchdog"));
    }

    [Fact]
    public void WatchdogKillsTheActiveScriptAndFailsWithBothOutputTails()
    {
        var output = new RecordingOutput();
        var watchdog = new ReportSupervisorTestWatchdog(
            output,
            TimeSpan.FromMilliseconds(100));
        using var process = new Process
        {
            StartInfo = new ProcessStartInfo
            {
                FileName = "/bin/bash",
                UseShellExecute = false,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
            },
        };
        process.StartInfo.ArgumentList.Add("-c");
        process.StartInfo.ArgumentList.Add("printf 'watchdog-out\\n'; printf 'watchdog-err\\n' >&2; sleep 60");

        Assert.True(process.Start());
        watchdog.Track(process);
        Assert.True(process.WaitForExit(5_000), "watchdog did not terminate the active script");

        var failure = Assert.Throws<XunitException>(() => watchdog.Dispose());
        Assert.Contains("stdout tail", failure.Message, StringComparison.Ordinal);
        Assert.Contains("watchdog-out", failure.Message, StringComparison.Ordinal);
        Assert.Contains("stderr tail", failure.Message, StringComparison.Ordinal);
        Assert.Contains("watchdog-err", failure.Message, StringComparison.Ordinal);
        Assert.Contains("watchdog-out", output.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void ProcessRunnerTimesOutWhenAnExitedParentLeavesAnOutputPipeOpen()
    {
        var stopwatch = Stopwatch.StartNew();

        Assert.Throws<TimeoutException>(() => ReportSupervisorTestProcessRunner.Run(
            "/bin/bash",
            ["-c", "sleep 2 &"],
            Directory.GetCurrentDirectory(),
            TimeSpan.FromMilliseconds(100),
            4096));

        Assert.True(stopwatch.Elapsed < TimeSpan.FromSeconds(1), stopwatch.Elapsed.ToString());
    }

    private sealed class RecordingOutput : ITestOutputHelper
    {
        private readonly List<string> lines = [];

        internal string Text => string.Join('\n', lines);

        public void WriteLine(string message) => lines.Add(message);

        public void WriteLine(string format, params object[] args) =>
            lines.Add(string.Format(System.Globalization.CultureInfo.InvariantCulture, format, args));
    }
}
