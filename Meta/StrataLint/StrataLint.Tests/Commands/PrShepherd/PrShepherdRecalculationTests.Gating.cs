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
            "DRYRUN #1 BEHIND stale derivations -> ensure worktree",
            "DRYRUN #1 fetch origin/dev and origin/feature; verify observed OIDs",
            "DRYRUN #1 checkout feature; merge origin/dev (derived conflicts take dev)",
            "DRYRUN #1 run make lean-report",
            "DRYRUN #1 run make emit",
            "DRYRUN #1 run make ingest BASE=origin/dev",
            "DRYRUN #1 run echo-verify --emit --base origin/dev (atomic install)",
            "DRYRUN #1 run make emit-check BASE=origin/dev",
            $"DRYRUN #1 commit: {CommitSubject}",
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
        var root = FindRepositoryRoot();
        var script = File.ReadAllText(Path.Combine(root, ShepherdScriptPath));

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
}
