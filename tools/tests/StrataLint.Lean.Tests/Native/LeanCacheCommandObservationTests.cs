using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class LeanCacheCommandObservationTests
{
    [Fact]
    public void CacheChildOutputIsLiveAndRawExitIsPreserved()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var phases = Path.Combine(temporary.Path, "phases");
        var stdout = Path.Combine(temporary.Path, "stdout");
        var stderr = Path.Combine(temporary.Path, "stderr");
        var observation = new StrataLint.EngineeringScope.LeanCacheCommandObservation(phases, stdout, stderr);
        var runner = new StrataLint.EngineeringScope.ProductionWorktreeProcessRunner(observation: observation);
        using var forwardedOut = new MemoryStream();
        using var forwardedError = new MemoryStream();
        var result = runner.Run("python3", ["-c", """
            import sys, time
            from pathlib import Path
            print('raw stdout', flush=True)
            print('raw stderr', file=sys.stderr, flush=True)
            while not all(Path(p).exists() and text in Path(p).read_text()
                          for p, text in zip(sys.argv[1:], ['raw stdout', 'raw stderr'])):
                time.sleep(0.01)
            sys.exit(37)
            """, stdout, stderr], temporary.Path, TestBudgets.ReportSupervisorHangGuard,
                observation.Output(forwardedOut), observation.Error(forwardedError));
        Assert.Equal(37, result.ExitCode);
        Assert.Equal("raw stdout\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Equal("raw stderr\n", Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal("raw stdout\n", File.ReadAllText(stdout));
        Assert.Equal("raw stderr\n", File.ReadAllText(stderr));
        Assert.Equal(result.StandardOutput, forwardedOut.ToArray());
        Assert.Equal(result.StandardError, forwardedError.ToArray());
        using var last = System.Text.Json.JsonDocument.Parse(File.ReadLines(phases).Last());
        Assert.Equal(37, last.RootElement.GetProperty("raw_exit").GetInt32());
        Assert.Equal("finish", last.RootElement.GetProperty("boundary").GetString());
    }

    [Fact]
    public void UnwritableDiagnosticsPreserveRawStreamsAndCancellation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var blocked = Path.Combine(temporary.Path, "blocked");
        File.WriteAllText(blocked, "regular file");
        var observation = new StrataLint.EngineeringScope.LeanCacheCommandObservation(
            Path.Combine(blocked, "phases"), Path.Combine(blocked, "stdout"), Path.Combine(blocked, "stderr"));
        var runner = new StrataLint.EngineeringScope.ProductionWorktreeProcessRunner(observation: observation);
        var result = runner.Run("python3", ["-c",
            "import sys; print('raw stdout'); print('raw stderr', file=sys.stderr); sys.exit(41)"],
            temporary.Path, TestBudgets.ReportSupervisorHangGuard);
        Assert.Equal(41, result.ExitCode);
        Assert.Equal("raw stdout\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Equal("raw stderr\n", Encoding.UTF8.GetString(result.StandardError));
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var cancelled = new StrataLint.EngineeringScope.ProductionWorktreeProcessRunner(cancellation.Token, observation);
        Assert.Throws<OperationCanceledException>(() => cancelled.Run("python3", ["-c", "pass"],
            temporary.Path, TestBudgets.ReportSupervisorHangGuard));
    }

}
