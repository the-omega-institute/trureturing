using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReportSupervisorScriptTests
{
    [Fact]
    public void CpuActiveMathlibScalePhaseOutlivingTheStallThresholdIsNeverKilled()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.Run(
            fixture.CpuOnlyWorker,
            fixture.AcceleratedWatchdogEnvironment(stepSeconds: 20));

        Assert.Equal(0, result.ExitCode);
        Assert.DoesNotContain(
            "no Lean progress",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [Fact]
    public void WholeSecondCpuSamplingDoesNotKillALowDutyCycleProducer()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.Run(
            fixture.QuantizedLowDutyWorker,
            $"PATH={fixture.ClockBin}:{fixture.Root}:{fixture.HostPath}",
            $"STRATALINT_TEST_CLOCK_FILE={fixture.WatchdogClockFile}",
            "STRATALINT_TEST_CLOCK_STEP_SECONDS=5",
            "STRATALINT_TEST_QUANTIZED_CPU=1",
            "STRATALINT_REPORT_STALL_TIMEOUT_SECONDS=2",
            "STRATALINT_REPORT_STALL_WINDOW_SECONDS=60",
            "STRATALINT_REPORT_STALL_WINDOW_COUNT=3");

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
        Assert.True(
            File.Exists(fixture.MetricsLog),
            $"stdout: {Encoding.UTF8.GetString(result.StandardOutput)}\n"
            + $"stderr: {Encoding.UTF8.GetString(result.StandardError)}\n"
            + $"clock-link: {new FileInfo(fixture.ClockDate).LinkTarget ?? "regular"}");
        Assert.Equal(2, fixture.ReadSingleMetricExitCode());
    }

    [Fact]
    public void ManualBashInvocationWatchdogFailureReturnsAndRecordsExactlyTwo()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.RunManualSingleProcess();

        Assert.Equal(2, result.ExitCode);
        Assert.True(
            File.Exists(fixture.MetricsLog),
            $"stdout: {Encoding.UTF8.GetString(result.StandardOutput)}\n"
            + $"stderr: {Encoding.UTF8.GetString(result.StandardError)}\n"
            + $"clock-link: {new FileInfo(fixture.ClockDate).LinkTarget ?? "regular"}");
        Assert.Equal(2, fixture.ReadSingleMetricExitCode());
    }

    [Fact]
    public void StalledProducerIsKilledAsInfrastructureFailureAndReleasesSlot()
    {
        using var fixture = new LeaseWatchdogFixture();

        var stalled = fixture.Run(
            fixture.SleepWorker,
            fixture.AcceleratedWatchdogEnvironment(stepSeconds: 60));

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
            fixture.AcceleratedWatchdogEnvironment(stepSeconds: 20));

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void PipeOutputKeepsAProducerAliveWithoutOleanChanges()
    {
        using var fixture = new LeaseWatchdogFixture();

        var result = fixture.Run(
            fixture.PipeProgressWorker,
            fixture.AcceleratedWatchdogEnvironment(stepSeconds: 20));

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
            fixture.AcceleratedWatchdogEnvironment(stepSeconds: 20));

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void FaultInjectedPartialLakeArtifactIsRebuiltAndImportableOnTheNextBuild()
    {
        using var fixture = new LeaseWatchdogFixture();

        var interrupted = fixture.Run(
            fixture.PartialLakeArtifactWorker,
            fixture.AcceleratedWatchdogEnvironment(stepSeconds: 60));

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
}
