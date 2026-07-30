namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void ConflictingWithSourceConflictReachesLocalAuthorityAndAlertsOnceWithoutPush()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(sourceConflict: true);

        var result = fixture.Run(duplicatePrRow: true, conflicting: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.True(Directory.Exists(fixture.CacheWorktree));
        Assert.Equal(["worktree"], fixture.MutationCalls());
        Assert.Equal(
            1,
            result.Log.Split(
                "ALERT #1 CONFLICTING head=feature 需语义合并(派 shepherd lane,本器不代解)",
                StringSplitOptions.None).Length - 1);
    }

    [Fact]
    public void ConflictingWithOnlyDerivedConflictsRecalculatesAndPushesNonForce()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.Run(
            expiryFingerprint: false,
            duplicatePrRow: true,
            conflicting: true);

        Assert.Equal(0, result.ExitCode);
        Assert.NotEqual(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Equal("dev choice\n", fixture.ShowRemote("Generated/dev-choice.md"));
        Assert.Equal(
            ["worktree", "lean-report", "emit", "ingest", "echo-verify", "emit-check", "push"],
            fixture.MutationCalls());
        Assert.Contains(
            "SWEEP #1 本地 merge+regen+push 完成 head=feature",
            result.Log,
            StringComparison.Ordinal);
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
}
