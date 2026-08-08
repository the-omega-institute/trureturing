namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void DryRunPrintsExpiredDerivationPlanWithoutMutatingGitOrGithub()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.Run(dryRun: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.False(Directory.Exists(fixture.CacheWorktree));
        Assert.Empty(fixture.MutationCalls());
        AssertInOrder(
            result.Log,
            "DRYRUN #1 RECALCULATE -> ensure worktree",
            "DRYRUN #1 fetch origin/dev and origin/feature; verify observed OIDs",
            "DRYRUN #1 checkout feature; merge origin/dev (derived conflicts take dev)",
            "DRYRUN #1 run make lean-report",
            "DRYRUN #1 run make emit",
            "DRYRUN #1 run make ingest BASE=origin/dev",
            "DRYRUN #1 run echo-verify --emit --base origin/dev (atomic install)",
            $"DRYRUN #1 commit/re-emit to fixed point (max 3 rounds): {CommitSubject}",
            "DRYRUN #1 run make emit-check BASE=origin/dev",
            "DRYRUN #1 push HEAD:refs/heads/feature (non-force)");
    }

    [Fact]
    public void DryRunOpenPrintsPlanWithoutCreatingOrArmingPullRequest()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.RunOpenDryRun();

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(fixture.MutationCalls());
        Assert.Contains(
            "DRYRUN OPEN head=feature title=fixture title -> create PR + arm auto-merge",
            result.Log,
            StringComparison.Ordinal);
    }

    [Fact]
    public void BehindWithoutExpiryFingerprintRetainsExactUpdateBranchBehavior()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.Run(expiryFingerprint: false);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            ["gh-api:-X PUT repos/the-omega-institute/trureturing/pulls/1/update-branch"],
            fixture.MutationCalls());
        Assert.EndsWith(
            "SWEEP #1 BEHIND -> update-branch(本地身份,checks 会触发)\n",
            result.Log,
            StringComparison.Ordinal);
        Assert.False(Directory.Exists(fixture.CacheWorktree));
    }

    [Fact]
    public void PrDiffFailureIsUnknownAndSkipsThePullRequestWithAnAlert()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.Run(diffFailure: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Empty(fixture.MutationCalls());
        Assert.False(Directory.Exists(fixture.CacheWorktree));
        Assert.Contains(
            "ALERT #1 PR file classification=UNKNOWN; skip this sweep",
            result.Log,
            StringComparison.Ordinal);
        Assert.DoesNotContain("RECALCULATE", result.Log, StringComparison.Ordinal);
        Assert.DoesNotContain("update-branch", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void FingerprintsSplitAcrossWorkflowJobsRetainUpdateBranchBehavior()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.Run(splitFingerprintAcrossJobs: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            ["gh-api:-X PUT repos/the-omega-institute/trureturing/pulls/1/update-branch"],
            fixture.MutationCalls());
        Assert.False(Directory.Exists(fixture.CacheWorktree));
    }

    [Fact]
    public void ScriptClassifierUsesLatestFailedAdmissionMachineFieldsAndAllExpiryTokens()
    {
        var script = ReadShepherdScripts();

        Assert.Contains("Content-addressed dev baseline admission", script, StringComparison.Ordinal);
        Assert.Contains("completedAt", script, StringComparison.Ordinal);
        Assert.Contains("startedAt // .completedAt", script, StringComparison.Ordinal);
        Assert.Contains("conclusion", script, StringComparison.Ordinal);
        Assert.Contains("detailsUrl", script, StringComparison.Ordinal);
        Assert.Contains("DIGEST_STATUS_INVALID", script, StringComparison.Ordinal);
        Assert.Contains("scribe-emissions", script, StringComparison.Ordinal);
        Assert.Contains("ECHO_VERIFY_INFRASTRUCTURE", script, StringComparison.Ordinal);
        Assert.Contains("residual", script, StringComparison.Ordinal);
        Assert.Contains("SHEPHERD_DRYRUN", script, StringComparison.Ordinal);
    }

    [Fact]
    public void DerivedConflictClassifierRetainsOnlyFrozenLedgerCompensation()
    {
        var script = ReadShepherdScripts();

        Assert.DoesNotContain("Meta/StrataLint/Generated/*", script, StringComparison.Ordinal);
        var classifier = script[script.IndexOf("is_derived_conflict()", StringComparison.Ordinal)..];
        classifier = classifier[..classifier.IndexOf("branch_slug()", StringComparison.Ordinal)];
        Assert.DoesNotContain(string.Join('/', "Evidence", "D5", "values.json"), classifier, StringComparison.Ordinal);
        Assert.DoesNotContain(string.Join('/', "Meta", "StrataLint", "Generated", "anchor-catalog.v1.json"), classifier, StringComparison.Ordinal);
        Assert.DoesNotContain(string.Join('/', "Meta", "StrataLint", "Generated", "scribe-emissions.v1.json"), classifier, StringComparison.Ordinal);
        Assert.Contains("$FROZEN_LEDGER_PATH", classifier, StringComparison.Ordinal);
    }

    [Fact]
    public void DryRunNeverWritesNoCheckStateOrWakesPullRequest()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.RunWatch(noChecks: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(fixture.MutationCalls());
        Assert.False(Directory.Exists(fixture.StateDirectory));
        Assert.Equal(
            2,
            result.Log.Split("DRYRUN #1 head=", StringSplitOptions.None).Length - 1);
    }

    [Fact]
    public void StaleGithubBaseOidDoesNotPreventRecalculationWhenLocalBaseIsStable()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(staleBaseRefOid: true);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.NotEqual(fixture.GithubBaseRefOid, fixture.BaseHead);
        Assert.NotEqual(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Equal(
            ["worktree", "lean-report", "ledger-append", "lean-report", "ledger-reattest", "emit", "ingest", "echo-verify", "emit", "emit-check", "push"],
            fixture.MutationCalls());
        Assert.Contains("RECALCULATE -> 本地 merge+regen+push 完成", result.Log);
    }

    [Fact]
    public void HeadChangingDuringFetchStopsAndLogsExpectedAndActualOids()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(moveHeadDuringFetch: true);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.AttackerHead, fixture.RemoteHead());
        Assert.Equal(["worktree"], fixture.MutationCalls());
        Assert.Contains(
            $"head 已漂移 expected={fixture.OriginalHead[..12]} actual={fixture.AttackerHead[..12]}",
            result.Log,
            StringComparison.Ordinal);
        Assert.DoesNotContain("base 已漂移", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void BaseChangingDuringFetchStopsAndLogsExpectedAndActualOids()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(moveBaseDuringFetch: true);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Equal(["worktree"], fixture.MutationCalls());
        Assert.Contains(
            $"base 已漂移 expected={fixture.BaseHead[..12]} actual={fixture.MovedBaseHead[..12]}",
            result.Log,
            StringComparison.Ordinal);
        Assert.DoesNotContain("head 已漂移", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void SweepIsSkippedWhileTheGraphqlQuotaSitsBelowItsFloor()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(graphqlRemaining: "10");

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("SWEEP 跳过", result.Log, StringComparison.Ordinal);
        Assert.Empty(fixture.MutationCalls());
    }

    [Fact]
    public void AnUnreadableQuotaDoesNotStallTheSweep()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(graphqlRemaining: "unreadable");

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.DoesNotContain("SWEEP 跳过", result.Log, StringComparison.Ordinal);
        Assert.Contains("push", fixture.MutationCalls());
    }
}
