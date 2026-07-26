using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReportSupervisorScriptTests
{
    [Theory]
    [InlineData("Z+")]
    [InlineData("X")]
    public void DeadOnlyProcessGroupAllowsReclaim(string state)
    {
        using var fixture = new DeadOwnerObservationFixture();
        var members = fixture.RunProcessGroupMembers(99999999, state);
        Assert.Equal(0, members.ExitCode);
        Assert.Empty(members.StandardOutput);
        fixture.CreateSlotWithOwner("99999999|definitely-dead|0\n");
        _ = fixture.AttachEmptyProcessGroup();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.Root}:{fixture.HostPath}",
            $"STRATALINT_TEST_PS_DEAD_GROUP_STATE={state}",
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
}
