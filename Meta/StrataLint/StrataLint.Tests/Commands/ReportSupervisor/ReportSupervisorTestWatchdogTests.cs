using System.Diagnostics;
using Xunit.Sdk;

namespace StrataLint.Tests;

public sealed class ReportSupervisorTestWatchdogTests
{
    [Fact]
    public void TimeoutKillsTrackedProcessAndReportsCapturedError()
    {
        var watchdog = new ReportSupervisorTestWatchdog(TimeSpan.FromMilliseconds(100));
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
        process.StartInfo.ArgumentList.Add("printf 'watchdog-err\\n' >&2; sleep 60");

        try
        {
            Assert.True(process.Start());
            watchdog.Track(process);
            Assert.True(process.WaitForExit(5_000), "watchdog did not terminate the tracked process");

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
            watchdog.Dispose();
        }
    }
}
