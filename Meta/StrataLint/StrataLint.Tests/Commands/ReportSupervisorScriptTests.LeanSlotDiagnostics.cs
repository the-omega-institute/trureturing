using System.Text;

namespace StrataLint.Tests;

public sealed partial class ReportSupervisorScriptTests
{
    [Fact]
    public void ClaimedLeanSlotPersistsAttributableHolderMetadata()
    {
        using var fixture = new ReportSupervisorFixture();
        var earliestAcquisition = DateTimeOffset.UtcNow.ToUnixTimeSeconds();
        using var process = fixture.StartLongRunningProducer();

        try
        {
            fixture.WaitUntil(
                () => File.Exists(fixture.GrandchildPid),
                "worker did not publish its child pid");
            var slot = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
            var latestAcquisition = DateTimeOffset.UtcNow.ToUnixTimeSeconds();
            var physicalRootResult = fixture.RunExternalProcess(
                "/bin/pwd",
                ["-P"],
                fixture.Root,
                maximumOutputBytes: 4096);
            Assert.Equal(0, physicalRootResult.ExitCode);
            var physicalRoot = Encoding.UTF8.GetString(physicalRootResult.StandardOutput).Trim();

            Assert.StartsWith(
                process.Id.ToString(System.Globalization.CultureInfo.InvariantCulture) + "|",
                File.ReadAllText(Path.Combine(slot, "owner")),
                StringComparison.Ordinal);
            Assert.Equal("lean-producer\n", File.ReadAllText(Path.Combine(slot, "role")));
            Assert.Equal(physicalRoot + "\n", File.ReadAllText(Path.Combine(slot, "worktree")));
            Assert.Matches(
                "^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z\\n$",
                File.ReadAllText(Path.Combine(slot, "acquired-at")));
            Assert.InRange(
                long.Parse(
                    File.ReadAllText(Path.Combine(slot, "acquired-at-epoch")).Trim(),
                    System.Globalization.CultureInfo.InvariantCulture),
                earliestAcquisition,
                latestAcquisition);
        }
        finally
        {
            if (!process.HasExited)
            {
                var signal = fixture.RunExternalProcess(
                    "/bin/kill",
                    ["-TERM", process.Id.ToString(System.Globalization.CultureInfo.InvariantCulture)],
                    maximumOutputBytes: 4096);
                Assert.Equal(0, signal.ExitCode);
                fixture.WaitForExit(process, "supervisor did not exit after SIGTERM");
            }
        }
    }

    [Fact]
    public void LiveSlotTimeoutReportsAttributableHolderMetadata()
    {
        using var fixture = new ReportSupervisorFixture();
        var liveLock = Path.Combine(fixture.StateRoot, "slots", "slot-1.lock");
        var acquiredAtEpoch = DateTimeOffset.UtcNow.AddSeconds(-75).ToUnixTimeSeconds();
        var acquiredAt = DateTimeOffset.FromUnixTimeSeconds(acquiredAtEpoch)
            .UtcDateTime.ToString(
                "yyyy-MM-dd'T'HH:mm:ss'Z'",
                System.Globalization.CultureInfo.InvariantCulture);
        Directory.CreateDirectory(liveLock);
        File.WriteAllText(
            Path.Combine(liveLock, "owner"),
            Environment.ProcessId.ToString(System.Globalization.CultureInfo.InvariantCulture) + "\n",
            new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(liveLock, "role"), "c0-renew\n", new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(liveLock, "worktree"), fixture.Root + "\n", new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(liveLock, "acquired-at"), acquiredAt + "\n", new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(liveLock, "acquired-at-epoch"),
            acquiredAtEpoch.ToString(System.Globalization.CultureInfo.InvariantCulture) + "\n",
            new UTF8Encoding(false));

        var result = fixture.RunWithEnvironment(
            "lean-producer",
            leanSlot: true,
            fixture.ScratchWriter,
            "STRATALINT_LOCK_TIMEOUT_SECONDS=1");

        Assert.Equal(2, result.ExitCode);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("report-supervisor: Lean slot holder", error, StringComparison.Ordinal);
        Assert.Contains($"identity={Environment.ProcessId}", error, StringComparison.Ordinal);
        Assert.Contains($"acquired_at={acquiredAt}", error, StringComparison.Ordinal);
        Assert.Contains("role=c0-renew", error, StringComparison.Ordinal);
        Assert.Contains($"worktree={fixture.Root}", error, StringComparison.Ordinal);
        var heldSeconds = System.Text.RegularExpressions.Regex.Match(
            error,
            @"held_seconds=([0-9]+)",
            System.Text.RegularExpressions.RegexOptions.CultureInvariant);
        Assert.True(heldSeconds.Success, $"hold duration missing from stderr: {error}");
        Assert.True(
            long.Parse(heldSeconds.Groups[1].Value, System.Globalization.CultureInfo.InvariantCulture) >= 75,
            $"hold duration was shorter than the persisted acquisition time: {error}");
    }
}
