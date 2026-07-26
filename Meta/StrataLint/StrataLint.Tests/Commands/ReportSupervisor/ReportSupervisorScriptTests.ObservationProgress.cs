using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReportSupervisorScriptTests
{
    [ReportFact]
    public void CpuActiveMathlibScalePhaseOutlivingTheStallThresholdIsNeverKilled()
    {
        using var fixture = new DeadOwnerObservationFixture();

        var result = fixture.Run(
            fixture.CpuOnlyWorker,
            fixture.AcceleratedObservationEnvironment(stepSeconds: 20));

        Assert.Equal(0, result.ExitCode);
        Assert.DoesNotContain(
            "no Lean progress",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [ReportFact]
    public void WholeSecondCpuSamplingDoesNotKillALowDutyCycleProducer()
    {
        using var fixture = new DeadOwnerObservationFixture();

        var result = fixture.Run(
            fixture.QuantizedLowDutyWorker,
            $"PATH={fixture.ClockBin}:{fixture.Root}:{fixture.HostPath}",
            $"STRATALINT_TEST_CLOCK_FILE={fixture.ObservationClockFile}",
            "STRATALINT_TEST_CLOCK_STEP_SECONDS=5",
            "STRATALINT_TEST_QUANTIZED_CPU=1",
            "STRATALINT_REPORT_STALL_WINDOW_SECONDS=60",
            "STRATALINT_REPORT_STALL_WINDOW_COUNT=3");

        Assert.Equal(0, result.ExitCode);
        Assert.DoesNotContain(
            "no Lean progress",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
    }

    [ReportFact]
    public void StalledProducerIsObservedWithoutBeingKilled()
    {
        using var fixture = new DeadOwnerObservationFixture();

        var observed = fixture.Run(
            fixture.QuantizedLowDutyWorker,
            fixture.AcceleratedObservationEnvironment(stepSeconds: 60));

        Assert.Equal(0, observed.ExitCode);
        var standardError = Encoding.UTF8.GetString(observed.StandardError);
        Assert.True(
            standardError.Contains("stall observed", StringComparison.OrdinalIgnoreCase),
            standardError);
        Assert.False(fixture.SlotExists());
        Assert.Equal(0, fixture.Run(fixture.SuccessWorker).ExitCode);
    }

    [ReportFact]
    public void NewOleanFilesKeepAQuietProducerAlive()
    {
        using var fixture = new DeadOwnerObservationFixture();

        var result = fixture.Run(
            fixture.OleanProgressWorker,
            fixture.AcceleratedObservationEnvironment(stepSeconds: 20));

        Assert.Equal(0, result.ExitCode);
    }

    [ReportFact]
    public void PipeOutputKeepsAProducerAliveWithoutOleanChanges()
    {
        using var fixture = new DeadOwnerObservationFixture();

        var result = fixture.Run(
            fixture.PipeProgressWorker,
            fixture.AcceleratedObservationEnvironment(stepSeconds: 20));

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "progress-4",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [ReportFact]
    public void ProducerLogOutputKeepsAQuietUncompiledPhaseAlive()
    {
        using var fixture = new DeadOwnerObservationFixture();

        var result = fixture.Run(
            fixture.LogProgressWorker,
            fixture.AcceleratedObservationEnvironment(stepSeconds: 20));

        Assert.Equal(0, result.ExitCode);
    }
}
