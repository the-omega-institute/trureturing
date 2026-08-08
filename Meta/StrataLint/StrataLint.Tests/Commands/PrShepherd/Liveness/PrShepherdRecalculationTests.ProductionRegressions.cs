namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void StatusFromAnotherSnapshotReportsTheLiveOwnersProgress()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var started = fixture.RunStart(intervalSeconds: 30, maxCycles: 2);
        Assert.True(
            started.ExitCode == 0,
            $"exit={started.ExitCode}\nlog:\n{started.Log}\nartifacts:\n{string.Join("\n---\n", fixture.StepArtifactContents())}");
        fixture.WaitForWatchPhase("waiting");
        var expectedProgress = fixture.WatchStateField("last_progress_at");

        var status = fixture.RunStatusFromAnotherSnapshot();

        Assert.Equal(0, status.ExitCode);
        Assert.StartsWith("status=alive ", status.Output, StringComparison.Ordinal);
        Assert.Contains($"last_progress_at={expectedProgress}", status.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void BackgroundWatchWritesEachAuditEventExactlyOnce()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var started = fixture.RunStart(intervalSeconds: 30, maxCycles: 2);
        Assert.Equal(0, started.ExitCode);
        fixture.WaitForAuditFragment("WATCH cycle=1 loaded_script_blob=");

        var matchingEvents = fixture.AuditLogLines()
            .Count(line => line.Contains("WATCH cycle=1 loaded_script_blob=", StringComparison.Ordinal));

        Assert.Equal(1, matchingEvents);
    }

    [Fact]
    public void ChildOutputIsIsolatedInAStepArtifactInsteadOfTheAuditLog()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var started = fixture.RunStart(
            intervalSeconds: 30,
            maxCycles: 2,
            dryRun: true,
            environment: new Dictionary<string, string>
            {
                ["PR_TEST_CHILD_OUTPUT"] = "1",
            });
        Assert.Equal(0, started.ExitCode);
        fixture.WaitForChildOutput();

        var audit = fixture.AuditLog();
        Assert.DoesNotContain("fixture-child-stdout", audit, StringComparison.Ordinal);
        Assert.DoesNotContain("fixture-child-stderr", audit, StringComparison.Ordinal);
        Assert.All(
            fixture.AuditLogLines(),
            line => Assert.Matches("^[0-9]{4}-[0-9]{2}-[0-9]{2} [0-9]{2}:[0-9]{2}:[0-9]{2} ", line));
        Assert.Contains(
            fixture.StepArtifactContents(),
            contents => contents.Contains("fixture-child-stdout", StringComparison.Ordinal));
        Assert.Contains(
            fixture.StepArtifactContents(),
            contents => contents.Contains("fixture-child-stderr", StringComparison.Ordinal));
        Assert.Contains(" stdout_artifact=", audit, StringComparison.Ordinal);
    }

    [Fact]
    public void AuditLogRotationHonorsTheConfiguredBound()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var started = fixture.RunStart(
            intervalSeconds: 30,
            maxCycles: 2,
            dryRun: false,
            environment: new Dictionary<string, string>
            {
                ["PR_SHEPHERD_LOG_MAX_BYTES"] = "512",
                ["PR_SHEPHERD_LOG_BACKUPS"] = "2",
            });
        Assert.Equal(0, started.ExitCode);
        fixture.StopWatch();

        var logFiles = fixture.AuditLogFiles();
        Assert.Contains(logFiles, path => path.EndsWith(".1", StringComparison.Ordinal));
        Assert.True(logFiles.Length <= 3, $"unexpected audit logs: {string.Join(", ", logFiles)}");
        Assert.All(logFiles, path => Assert.True(new FileInfo(path).Length <= 1_024, path));
    }

    [Fact]
    public void WatchReloadsTheAtomicCompositeFromAdvancingRemoteDev()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var reloadProbe = fixture.ReloadProbePath;
        var started = fixture.RunStart(
            intervalSeconds: 2,
            maxCycles: 3,
            environment: new Dictionary<string, string>
            {
                ["PR_TEST_RELOAD_PROBE"] = reloadProbe,
            });
        Assert.Equal(0, started.ExitCode);
        fixture.WaitForWatchCycle(1);

        fixture.AdvanceRemoteDevWithNewShepherdModule();
        fixture.WaitForWatchCycle(2);
        fixture.WaitForAuditFragment("WATCH reloaded cycle=2");

        Assert.True(File.Exists(reloadProbe), "the helper added to remote dev was not loaded");
        var loadedBlobs = fixture.AuditLogLines()
            .Select(line => line.Split("loaded_script_blob=", 2, StringSplitOptions.None))
            .Where(parts => parts.Length == 2)
            .Select(parts => parts[1].Split(' ', 2)[0])
            .Distinct(StringComparer.Ordinal)
            .ToArray();
        Assert.True(loadedBlobs.Length >= 2, $"loaded blobs: {string.Join(", ", loadedBlobs)}");
        Assert.Contains("WATCH SCRIPT CHANGED", fixture.AuditLog(), StringComparison.Ordinal);
    }
}
