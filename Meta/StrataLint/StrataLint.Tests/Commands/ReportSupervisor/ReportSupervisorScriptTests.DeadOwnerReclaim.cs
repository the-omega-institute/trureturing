using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReportSupervisorScriptTests
{
    [Theory]
    [InlineData("Z+")]
    [InlineData("X")]
    public void DeadOnlyLinuxProcessGroupAllowsReclaim(string state)
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachSyntheticProcStat(
            424242,
            state[0],
            parentPid: 1,
            processGroupId: 99999999,
            starttime: 12345);
        var members = fixture.RunProcessGroupMembersFromProc(99999999);
        Assert.Equal(0, members.ExitCode);
        Assert.Empty(members.StandardOutput);
        fixture.CreateSlotWithOwner("99999999|definitely-dead|0\n");
        _ = fixture.AttachEmptyProcessGroup();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.Root}:{fixture.HostPath}",
            $"STRATALINT_TEST_PS_DEAD_GROUP_STATE={state}",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=3");

        Assert.True(
            result.ExitCode == 0,
            $"exit: {result.ExitCode}\n"
            + $"stdout: {Encoding.UTF8.GetString(result.StandardOutput)}\n"
            + $"stderr: {Encoding.UTF8.GetString(result.StandardError)}");
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
            $"99999999|99999999|{EmptyGroupLeaderStartIdentity()}\n",
            new UTF8Encoding(false));
        var result = BoundedProcessRunner.Run(
            "bash",
            [fixture.ConcurrentDriver, fixture.Supervisor, fixture.ProducerWorker,
             fixture.MetricsLog, fixture.StateRoot, fixture.ActiveMarker, fixture.OverlapMarker,
             fixture.ConcurrentRelease, $"{fixture.Root}:{fixture.HostPath}"],
            fixture.Root,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

        Assert.True(
            result.ExitCode == 0,
            $"exit: {result.ExitCode}\n"
            + $"stdout: {Encoding.UTF8.GetString(result.StandardOutput)}\n"
            + $"stderr: {Encoding.UTF8.GetString(result.StandardError)}");
        Assert.False(File.Exists(fixture.OverlapMarker));
        Assert.Equal(2, fixture.ReadMetrics().Count);
    }
}
