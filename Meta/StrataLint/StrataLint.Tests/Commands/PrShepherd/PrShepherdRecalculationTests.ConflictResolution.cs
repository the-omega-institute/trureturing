using StrataLint.Engine;

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
        Assert.Equal("reemitted choice\n", fixture.ShowRemote("Generated/dev-choice.md"));
        Assert.Equal(
            [
                "worktree",
                "local-merge",
                "lean-report",
                "emit",
                "ingest",
                "echo-verify",
                "ledger-append",
                "emit",
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
    public void FrozenLedgerConflictIsRebuiltInsteadOfAlertingAsASemanticConflict()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(conflicting: true, ledgerConflict: true);

        var result = fixture.Run(expiryFingerprint: false, duplicatePrRow: true);

        Assert.Equal(0, result.ExitCode);
        Assert.NotEqual(fixture.OriginalHead, fixture.RemoteHead());
        Assert.DoesNotContain("ALERT #1 CONFLICTING", result.Log, StringComparison.Ordinal);
        Assert.Contains("ledger-append", fixture.MutationCalls());
        Assert.Contains("push", fixture.MutationCalls());
    }

    [Fact]
    public void RebuiltLedgerTakesTheDevSideBeforeReattestation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(conflicting: true, ledgerConflict: true);

        var result = fixture.Run(expiryFingerprint: false, duplicatePrRow: true);

        Assert.Equal(0, result.ExitCode);
        var ledger = fixture.ShowRemote(FrozenLedgerChangeClassifier.LedgerPath);
        Assert.Contains("dev-freeze", ledger, StringComparison.Ordinal);
        Assert.DoesNotContain("feature-freeze", ledger, StringComparison.Ordinal);
    }

    [Fact]
    public void FrozenLedgerConflictUsesBaseAppendThenCandidateReattestationBeforeBalancedEmission()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(conflicting: true, ledgerConflict: true);

        var result = fixture.Run(expiryFingerprint: false, duplicatePrRow: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            [
                "worktree",
                "local-merge",
                "lean-report",
                "ledger-append",
                "lean-report",
                "ledger-reattest",
                "emit",
                "ingest",
                "echo-verify",
                "emit",
                "emit-check",
                "push",
            ],
            fixture.MutationCalls());
        Assert.Equal(
            [
                "lean-report:base trureturing",
                "ledger-append:base-trureturing:new-report:dev-ledger",
                "lean-report:candidate trureturing",
                "ledger-reattest:candidate-trureturing:new-report:appended-ledger",
                "emit:dev-projection",
                "emit-check:balanced",
            ],
            fixture.LedgerObservations());
        var ledger = fixture.ShowRemote(FrozenLedgerChangeClassifier.LedgerPath);
        Assert.Contains("dev-freeze", ledger, StringComparison.Ordinal);
        Assert.Contains("appended-under-base", ledger, StringComparison.Ordinal);
        Assert.Contains("reattested-candidate", ledger, StringComparison.Ordinal);
        Assert.DoesNotContain("feature-freeze", ledger, StringComparison.Ordinal);
        Assert.Equal("candidate trureturing\n", fixture.ShowRemote("Trureturing.lean"));
        Assert.Equal("reemitted choice\n", fixture.ShowRemote("Generated/dev-choice.md"));
    }

    [Fact]
    public void FrozenLedgerConflictAlertsAndDoesNotPushWhenFinalEmitCheckIsUnbalanced()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(
            conflicting: true,
            ledgerConflict: true,
            failingTarget: "emit-check");

        var result = fixture.Run(expiryFingerprint: false);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Equal(
            [
                "worktree",
                "local-merge",
                "lean-report",
                "ledger-append",
                "lean-report",
                "ledger-reattest",
                "emit",
                "ingest",
                "echo-verify",
                "emit",
                "emit-check",
            ],
            fixture.MutationCalls());
        Assert.Contains("ALERT #1 emit-check 失败,不 push", result.Log, StringComparison.Ordinal);
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
