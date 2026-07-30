namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void ActiveBranchLockPreventsConcurrentWorktreeMutation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var plan = fixture.Run(dryRun: true);
        fixture.HoldBranchLock(DryRunWorktreeName(plan.Log));

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Empty(fixture.MutationCalls());
        Assert.Contains("已有重算实例,跳过本轮", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void SanitizedBranchSlugsRemainCollisionResistant()
    {
        if (OperatingSystem.IsWindows()) return;
        using var slash = new ShepherdFixture(headBranch: "topic/a");
        var slashResult = slash.Run(dryRun: true);
        var slashWorktree = DryRunWorktreeName(slashResult.Log);
        using var literal = new ShepherdFixture(headBranch: slashWorktree[3..]);
        var literalResult = literal.Run(dryRun: true);

        Assert.Equal(0, slashResult.ExitCode);
        Assert.Equal(0, literalResult.ExitCode);
        Assert.NotEqual(slashWorktree, DryRunWorktreeName(literalResult.Log));
    }

    [Fact]
    public async Task ConcurrentStaleLockReclamationAllowsOnlyOneRecalculation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(
            pauseWorktreeCreation: true,
            delayFirstLockOwnerRead: true);
        var plan = fixture.Run(dryRun: true);
        fixture.CreateStaleBranchLock(DryRunWorktreeName(plan.Log));

        var results = await Task.WhenAll(
            Task.Run(() => fixture.Run()),
            Task.Run(() => fixture.Run()));

        Assert.All(results, result => Assert.Equal(0, result.ExitCode));
        Assert.Equal(1, fixture.MutationCalls().Count(call => call == "push"));
        Assert.Equal(1, fixture.CountCommitsWithSubject(CommitSubject));
    }

    [Fact]
    public void StaleLockReclamationUsesAtomicRenameOwnership()
    {
        var root = FindRepositoryRoot();
        var script = File.ReadAllText(Path.Combine(root, ShepherdScriptPath));

        AssertInOrder(
            script,
            "mkdir \"$reap\"",
            "owner=\"$(cat \"$lock/pid\"",
            "mv \"$lock\" \"$stale\"");
    }

    [Fact]
    public void WatchRestartsCycleBudgetWhileAnArmedPullRequestRemainsOpen()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.RunWatch();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            2,
            result.Log.Split(
                "DRYRUN #1 RECALCULATE -> ensure worktree",
                StringSplitOptions.None).Length - 1);
        Assert.Contains(
            "WATCH renew(1 轮耗尽,仍有 open 且 auto-merge armed PR,重启计数)",
            result.Log,
            StringComparison.Ordinal);
        Assert.EndsWith(
            "WATCH end(1 轮耗尽,无 open auto-merge armed PR)\n",
            result.Log,
            StringComparison.Ordinal);
    }
}
