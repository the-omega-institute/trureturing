using System.Diagnostics;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReportSupervisorScriptTests
{
    [Theory]
    [InlineData("4242 (worker) S 1 4242", true)]
    [InlineData("4242 (worker with ) paren) Z 1 4242", false)]
    [InlineData("4242 (dead) X 1 4242", false)]
    public void LinuxProcStatDistinguishesRunningAndDeadStates(string stat, bool expected)
    {
        Assert.Equal(expected, ProcStatRepresentsRunning(stat));
    }

    [Theory]
    [InlineData('S', 0)]
    [InlineData('Z', 1)]
    [InlineData('X', 1)]
    public void KillZeroIsQualifiedByLinuxProcState(char state, int expectedExit)
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachSyntheticProcStat(Environment.ProcessId, state);

        var result = fixture.RunProcessExists(Environment.ProcessId);

        Assert.Equal(expectedExit, result.ExitCode);
    }

    [Fact]
    public void UnreadableLinuxProcStateIsUnknown()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachUnreadableSyntheticProcStat(Environment.ProcessId);

        var result = fixture.RunProcessExists(Environment.ProcessId);

        Assert.Equal(2, result.ExitCode);
    }

    [Fact]
    public void LinuxProcessStartIdentityComesFromProcStatStarttime()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachSyntheticProcStat(
            Environment.ProcessId,
            'S',
            parentPid: 1,
            processGroupId: Environment.ProcessId,
            starttime: 987654321);

        var result = fixture.RunProcessStartIdentity(Environment.ProcessId);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("987654321", Encoding.UTF8.GetString(result.StandardOutput).Trim());
    }

    [Fact]
    public void LinuxProcessGroupMembersComeFromProcStatWithoutPs()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachSyntheticProcStat(4242, 'S', parentPid: 1, processGroupId: 9999, starttime: 101);
        fixture.AttachSyntheticProcStat(4243, 'Z', parentPid: 1, processGroupId: 9999, starttime: 102);
        fixture.AttachSyntheticProcStat(4244, 'S', parentPid: 1, processGroupId: 8888, starttime: 103);
        fixture.AttachSyntheticProcStat(4245, 'S', parentPid: 0, processGroupId: 0, starttime: 104);

        var result = fixture.RunProcessGroupMembersFromProc(9999);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("4242", Encoding.UTF8.GetString(result.StandardOutput).Trim());
    }

    [Fact]
    public void LinuxMarkerCandidatesAreBoundedByRecordedGroupAndLeaderStarttime()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachSyntheticProcStat(4242, 'S', parentPid: 50, processGroupId: 9999, starttime: 99);
        fixture.AttachSyntheticProcStat(4243, 'S', parentPid: 1, processGroupId: 8888, starttime: 101);
        fixture.AttachSyntheticProcStat(4244, 'S', parentPid: 1, processGroupId: 8888, starttime: 98);
        fixture.AttachSyntheticProcStat(4245, 'S', parentPid: 50, processGroupId: 8888, starttime: 102);
        fixture.AttachSyntheticProcStat(4246, 'Z', parentPid: 1, processGroupId: 9999, starttime: 103);

        var result = fixture.RunLinuxProcessCandidates(9999, leaderStarttime: 100);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("4242\n4243", Encoding.UTF8.GetString(result.StandardOutput).Trim());
    }

    [Fact]
    public void MalformedLinuxProcStatMakesStartIdentityUnknown()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachMalformedSyntheticProcStat(4242);

        var result = fixture.RunProcessStartIdentity(4242);

        Assert.Equal(1, result.ExitCode);
    }

    [Fact]
    public void ZeroLinuxProcStarttimeMakesStartIdentityUnknown()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachSyntheticProcStat(4242, 'S', starttime: 0);

        var result = fixture.RunProcessStartIdentity(4242);

        Assert.Equal(1, result.ExitCode);
    }

    [Fact]
    public void OldEpochOnLiveCanonicalOwnerDoesNotPermitReclaim()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.CreateTimestampedSlotOwnedByCurrentProcess(
            DateTimeOffset.UtcNow.AddMinutes(-1).ToUnixTimeMilliseconds());

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=3");

        Assert.Equal(2, result.ExitCode);
        Assert.True(fixture.SlotExists());
    }

    [Fact]
    public void ExtantLinuxProcDirectoryWithUnreadableStatIsUnknown()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachUnreadableSyntheticProcStat(4242);

        var result = fixture.RunLinuxProcStatSnapshot(4242);

        Assert.Equal(2, result.ExitCode);
    }

    [Fact]
    public void FallbackClaimantRecordsUnknownStartWhenPsIdentityIsUnreadable()
    {
        if (Directory.Exists("/proc")) return;
        using var fixture = new DeadOwnerObservationFixture();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.Root}:{fixture.HostPath}",
            "STRATALINT_TEST_PS_FAIL_ALL=1",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void OwnerRecordContainsPidStartAndEpoch()
    {
        using var fixture = new DeadOwnerObservationFixture();
        using var holder = fixture.Start(
            fixture.SleepWorker,
            fixture.SyntheticProcessEnvironment(fixture.SleepWorkerPidFile, 3));
        Assert.True(SpinWait.SpinUntil(
            () => fixture.SlotExists() && File.Exists(fixture.SleepWorkerPidFile),
            TimeSpan.FromSeconds(10)));
        var owner = File.ReadAllText(Path.Combine(fixture.Slot, "owner")).Trim().Split('|');

        Assert.Equal(3, owner.Length);
        Assert.Equal(
            holder.Id.ToString(System.Globalization.CultureInfo.InvariantCulture),
            owner[0]);
        Assert.False(string.IsNullOrWhiteSpace(owner[1]));
        Assert.True(long.Parse(owner[2], System.Globalization.CultureInfo.InvariantCulture) > 1_000_000_000_000);
    }

    [Fact]
    public void DeadOwnerFromMetadataCrashWindowIsReclaimed()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.CreateSlotWithOwner("99999999|definitely-dead|0\n");

        Assert.False(File.Exists(Path.Combine(fixture.Slot, "marker")));
        Assert.False(File.Exists(Path.Combine(fixture.Slot, "group")));

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=3");

        Assert.True(
            result.ExitCode == 0,
            $"stdout: {Encoding.UTF8.GetString(result.StandardOutput)}\n"
            + $"stderr: {Encoding.UTF8.GetString(result.StandardError)}");
    }

    [Fact]
    public void SigkillOrphanKeepsSlotUntilTheWholeProcessGroupIsDead()
    {
        using var fixture = new DeadOwnerObservationFixture();
        using var holder = fixture.Start(fixture.SleepWorker);
        Assert.True(SpinWait.SpinUntil(
            () => fixture.SlotMetadataIsPublished()
                && File.Exists(fixture.SleepWorkerPidFile),
            TimeSpan.FromSeconds(10)));
        var orphanPid = fixture.ReadSleepWorkerPid();
        var group = fixture.ReadProcessGroup();
        Assert.Equal(orphanPid, group.GroupId);
        Assert.Equal(orphanPid, group.LeaderPid);

        var signal = BoundedProcessRunner.Run(
            "/bin/kill",
            ["-KILL", holder.Id.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            fixture.Root,
            TimeSpan.FromSeconds(5),
            4096);
        Assert.Equal(0, signal.ExitCode);
        Assert.True(holder.WaitForExit(5_000));
        Assert.True(ProcessExists(orphanPid));

        var blocked = fixture.Run(
            fixture.SuccessWorker,
            fixture.SyntheticProcessEnvironment(fixture.SleepWorkerPidFile, 1));

        Assert.Equal(2, blocked.ExitCode);
        Assert.True(fixture.SlotExists());
        Assert.True(ProcessExists(orphanPid));
        fixture.KillProcess(orphanPid);
        Assert.True(SpinWait.SpinUntil(
            () => !ProcessExists(orphanPid),
            TimeSpan.FromSeconds(5)));

        var reclaimed = fixture.Run(
            fixture.SuccessWorker,
            fixture.SyntheticProcessEnvironment(fixture.SleepWorkerPidFile, 3));

        Assert.Equal(0, reclaimed.ExitCode);
    }

    [Fact]
    public void LiveClosedFdDescendantPreventsReclaimWithoutBeingKilled()
    {
        using var fixture = new DeadOwnerObservationFixture();
        using var holder = fixture.Start(
            fixture.ClosedFdDescendantWorker,
            fixture.SyntheticProcessEnvironment(fixture.ClosedFdDescendantPidFile, 3));
        Assert.True(SpinWait.SpinUntil(
            () => fixture.SlotExists()
                && fixture.SlotMetadataIsPublished()
                && File.Exists(fixture.ClosedFdLeaderPidFile)
                && File.Exists(fixture.ClosedFdDescendantPidFile),
            TimeSpan.FromSeconds(10)));
        var leaderPid = fixture.ReadPid(fixture.ClosedFdLeaderPidFile);
        var descendantPid = fixture.ReadPid(fixture.ClosedFdDescendantPidFile);
        var group = fixture.ReadProcessGroup();
        Assert.Equal(leaderPid, group.GroupId);
        Assert.Equal(leaderPid, group.LeaderPid);
        Assert.True(File.Exists(Path.Combine(fixture.Slot, "marker")));
        Assert.True(File.Exists(Path.Combine(fixture.Slot, "group")));

        fixture.KillProcess(holder.Id);
        fixture.KillProcess(leaderPid);
        Assert.True(holder.WaitForExit(5_000));
        Assert.True(ProcessExists(descendantPid));

        var blocked = fixture.Run(
            fixture.SuccessWorker,
            fixture.SyntheticProcessEnvironment(fixture.ClosedFdDescendantPidFile, 1));

        Assert.Equal(2, blocked.ExitCode);
        Assert.True(fixture.SlotExists());
        Assert.True(ProcessExists(descendantPid));
        File.Delete(fixture.ClosedFdDescendantHoldFile);
        Assert.True(SpinWait.SpinUntil(
            () => !ProcessExists(descendantPid),
            TimeSpan.FromSeconds(10)));

        var reclaimed = fixture.Run(
            fixture.SuccessWorker,
            fixture.SyntheticProcessEnvironment(fixture.ClosedFdDescendantPidFile, 3));

        Assert.Equal(0, reclaimed.ExitCode);
    }

    [Fact]
    public void MalformedNonemptyOwnerFailsClosed()
    {
        using var fixture = new DeadOwnerObservationFixture();
        var slot = fixture.CreateSlotWithOwner("not-an-owner\n");
        Directory.SetLastWriteTimeUtc(slot, DateTime.UtcNow.AddMinutes(-1));

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(Directory.Exists(slot));
    }

    [Fact]
    public void UnknownCanonicalLiveOwnerCannotBeReclaimedOnTimeout()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.CreateSlotWithOwner(
            $"{Environment.ProcessId}|unknown|{DateTimeOffset.UtcNow.AddMinutes(-1).ToUnixTimeMilliseconds()}\n");

        var result = fixture.Run(
            fixture.SuccessWorker,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        Assert.True(fixture.SlotExists());
    }

    [Fact]
    public void ThreeFieldOwnerWhosePidWasReusedIsReclaimed()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.CreateSlotWithOwner(
            $"{Environment.ProcessId}|not-the-current-start|{DateTimeOffset.UtcNow.ToUnixTimeMilliseconds()}\n");
        fixture.AttachEmptyProcessGroup();

        var result = fixture.Run(
            fixture.SuccessWorker,
            $"PATH={fixture.Root}:{fixture.HostPath}",
            $"STRATALINT_TEST_PS_REUSED_PID={Environment.ProcessId}",
            "STRATALINT_LOCK_TIMEOUT_SECONDS=5");

        Assert.True(
            result.ExitCode == 0,
            $"stdout: {Encoding.UTF8.GetString(result.StandardOutput)}\n"
            + $"stderr: {Encoding.UTF8.GetString(result.StandardError)}");
    }

    [Fact]
    public void MalformedSuccessfulFallbackProcessTableFailsClosed()
    {
        using var fixture = new DeadOwnerObservationFixture();

        var result = fixture.RunFallbackProcessGroupMembers(99999999);

        Assert.NotEqual(0, result.ExitCode);
    }

    [Fact]
    public void ProcMarkerScanConsidersEveryOpenDescriptorOfRecordedCandidate()
    {
        using var fixture = new DeadOwnerObservationFixture();
        var marker = Path.Combine(fixture.Root, "synthetic-process.marker");
        File.WriteAllText(marker, string.Empty, new UTF8Encoding(false));
        fixture.AttachSyntheticMarkerDescriptor(Environment.ProcessId, 37, marker);

        var result = fixture.RunMarkerScan(marker, Environment.ProcessId);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            Environment.ProcessId.ToString(System.Globalization.CultureInfo.InvariantCulture),
            Encoding.UTF8.GetString(result.StandardOutput).Trim());
    }

    [Fact]
    public void ProcMarkerScanDoesNotInspectUnrecordedPid()
    {
        using var fixture = new DeadOwnerObservationFixture();
        var marker = Path.Combine(fixture.Root, "synthetic-process.marker");
        File.WriteAllText(marker, string.Empty, new UTF8Encoding(false));
        fixture.AttachSyntheticMarkerDescriptor(4242, 9, marker);
        fixture.AttachSyntheticMarkerDescriptor(4243, 9, marker);

        var result = fixture.RunMarkerScan(marker, 4242);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("4242", Encoding.UTF8.GetString(result.StandardOutput).Trim());
    }

    [Fact]
    public void ProcProcessTreeFollowsParentPidAcrossNewProcessGroups()
    {
        using var fixture = new DeadOwnerObservationFixture();
        fixture.AttachSyntheticProcStat(4100, 'S', parentPid: 1, processGroupId: 4100);
        fixture.AttachSyntheticProcStat(4101, 'S', parentPid: 4100, processGroupId: 4101);
        fixture.AttachSyntheticProcStat(4102, 'S', parentPid: 4101, processGroupId: 4102);
        fixture.AttachSyntheticProcStat(4200, 'S', parentPid: 1, processGroupId: 4200);

        var result = fixture.RunLinuxProcessTree(4100);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            ["4100", "4101", "4102"],
            Encoding.UTF8.GetString(result.StandardOutput)
                .Split('\n', StringSplitOptions.RemoveEmptyEntries));
    }

}
