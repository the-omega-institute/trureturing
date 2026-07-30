namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void ConflictingWithSourceConflictReachesLocalAuthorityAndAlertsOnceWithoutPush()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(sourceConflict: true, conflicting: true);

        var result = fixture.Run(expiryFingerprint: false, duplicatePrRow: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.True(Directory.Exists(fixture.CacheWorktree));
        Assert.Equal(["worktree", "local-merge"], fixture.MutationCalls());
        Assert.Equal(
            1,
            result.Log.Split("ALERT #1 CONFLICTING", StringSplitOptions.None).Length - 1);
    }

    [Fact]
    public void ConflictingDryRunRoutesIntoRecalculationWithoutMutationOrCoarseAlert()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(conflicting: true);

        var result = fixture.Run(dryRun: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Empty(fixture.MutationCalls());
        Assert.False(Directory.Exists(fixture.CacheWorktree));
        Assert.False(Directory.Exists(fixture.StateDirectory));
        Assert.Contains("DRYRUN #1 RECALCULATE -> ensure worktree", result.Log);
        Assert.DoesNotContain("ALERT #1 CONFLICTING", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void ConflictingWithOnlyDerivedConflictsRecalculatesAndPushesNonForce()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(conflicting: true);

        var result = fixture.Run(expiryFingerprint: false, duplicatePrRow: true);

        Assert.Equal(0, result.ExitCode);
        var remoteHead = fixture.RemoteHead();
        Assert.NotEqual(fixture.OriginalHead, remoteHead);
        Assert.True(fixture.IsAncestor(fixture.OriginalHead, remoteHead));
        Assert.True(fixture.IsAncestor(fixture.BaseHead, remoteHead));
        Assert.Equal("dev choice\n", fixture.ShowRemote("Generated/dev-choice.md"));
        Assert.Equal(
            [
                "worktree",
                "local-merge",
                "lean-report",
                "emit",
                "ingest",
                "echo-verify",
                "emit-check",
                "push",
            ],
            fixture.MutationCalls());
        var completionLine = Assert.Single(
            result.Log.Split('\n', StringSplitOptions.RemoveEmptyEntries),
            static line => line.Contains("RECALCULATE", StringComparison.Ordinal));
        Assert.All(
            new[] { "SWEEP #1", "RECALCULATE", "head=feature" },
            token => Assert.Contains(token, completionLine, StringComparison.Ordinal));
        Assert.DoesNotContain("ALERT #1 CONFLICTING", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void DerivedConflictAcceptsDeletionFromDevBeforeReemission()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(devDeletesDerived: true);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.NotEqual(fixture.OriginalHead, fixture.RemoteHead());
        Assert.False(fixture.RemoteContains("Generated/dev-choice.md"));
        Assert.Contains("push", fixture.MutationCalls());
    }

    [Fact]
    public void NonConflictMergeFailureStopsBeforeDerivationAndPush()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failMergeWithoutConflict: true);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Equal(["worktree"], fixture.MutationCalls());
        Assert.Contains("merge origin/dev 失败,不 push", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void SemanticConflictAlertHasOneSourceOfTruth()
    {
        var root = FindRepositoryRoot();
        var script = File.ReadAllText(Path.Combine(root, ShepherdScriptPath));
        const string alert =
            "ALERT #$num CONFLICTING head=$head 需语义合并(派 shepherd lane,本器不代解)";

        Assert.Equal(1, script.Split(alert, StringSplitOptions.None).Length - 1);
    }
}
