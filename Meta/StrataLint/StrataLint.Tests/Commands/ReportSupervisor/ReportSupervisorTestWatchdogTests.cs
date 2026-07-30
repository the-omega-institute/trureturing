using System.Diagnostics;
using Xunit.Sdk;

namespace StrataLint.Tests;

public sealed class ReportSupervisorTestWatchdogTests
{
    [Fact]
    public void TimeoutKillsTrackedProcessAndReportsCapturedError()
    {
        using var fixture = new ReportSupervisorFixture();
        var ready = Path.Combine(fixture.Root, "watchdog-ready");
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
        process.StartInfo.ArgumentList.Add("printf 'watchdog-err\\n' >&2; touch \"$1\"; sleep 60");
        process.StartInfo.ArgumentList.Add("bash");
        process.StartInfo.ArgumentList.Add(ready);

        ReportSupervisorTestWatchdog? watchdog = null;
        try
        {
            Assert.True(process.Start());
            fixture.WaitUntil(
                () => File.Exists(ready),
                "tracked process did not publish its ready sentinel");
            watchdog = new ReportSupervisorTestWatchdog(TimeSpan.FromMilliseconds(100));
            watchdog.Track(process);
            fixture.WaitForExit(process, "watchdog did not terminate the tracked process");

            var failure = Assert.Throws<XunitException>(() => watchdog.Dispose());
            Assert.Contains("timed out", failure.Message, StringComparison.OrdinalIgnoreCase);
            Assert.Contains("watchdog-err", failure.Message, StringComparison.Ordinal);
        }
        finally
        {
            try
            {
                if (!process.HasExited) process.Kill(entireProcessTree: true);
            }
            catch (InvalidOperationException)
            {
                // The process exited concurrently with test cleanup.
            }
            watchdog?.Dispose();
        }
    }
}
