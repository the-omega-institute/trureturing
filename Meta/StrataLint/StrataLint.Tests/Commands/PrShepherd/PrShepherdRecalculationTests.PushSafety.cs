namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void ExpiredAdmissionReusesPersistentWorktreeAndRunsCanonicalChainOncePerSweep()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var first = fixture.Run(duplicatePrRow: true);

        Assert.Equal(0, first.ExitCode);
        var firstHead = fixture.RemoteHead();
        Assert.NotEqual(fixture.OriginalHead, firstHead);
        Assert.True(fixture.IsAncestor(fixture.BaseHead, firstHead));
        Assert.Equal("derived artifact\n", fixture.ShowRemote("Generated/artifact.md"));
        Assert.Equal(
            ["worktree", "lean-report", "emit", "ingest", "echo-verify", "emit-check", "push"],
            fixture.MutationCalls());
        Assert.Equal(1, fixture.CountCommitsWithSubject(CommitSubject));
        Assert.True(Directory.Exists(fixture.CacheWorktree));

        var firstBase = fixture.BaseHead;
        fixture.AdvanceDev();
        fixture.ClearMutationCalls();
        var skipped = fixture.Run();

        Assert.Equal(0, skipped.ExitCode);
        Assert.Equal(firstHead, fixture.RemoteHead());
        Assert.Empty(fixture.MutationCalls());
        Assert.Contains(
            $"base 已漂移 expected={firstBase[..12]} actual={fixture.BaseHead[..12]}",
            skipped.Log,
            StringComparison.Ordinal);

        var second = fixture.Run();

        Assert.Equal(0, second.ExitCode);
        var secondHead = fixture.RemoteHead();
        Assert.NotEqual(firstHead, secondHead);
        Assert.True(fixture.IsAncestor(fixture.BaseHead, secondHead));
        Assert.Equal(
            ["lean-report", "emit", "ingest", "echo-verify", "emit-check", "push"],
            fixture.MutationCalls());
        Assert.Equal(2, fixture.CountCommitsWithSubject(CommitSubject));
    }

    [Fact]
    public void EmitCheckFailureLeavesRemoteHeadUntouched()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(failingTarget: "emit-check");

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Equal(
            ["worktree", "lean-report", "emit", "ingest", "echo-verify", "emit-check"],
            fixture.MutationCalls());
        Assert.Contains("emit-check 失败,不 push", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void NonFastForwardPushIsAbandonedWithoutOverwritingConcurrentHead()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(moveHeadBeforePush: true);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.AttackerHead, fixture.RemoteHead());
        Assert.Contains("push 非 FF 被拒,放弃本轮(下轮重试)", result.Log, StringComparison.Ordinal);
        Assert.Equal(0, fixture.CountCommitsWithSubject(CommitSubject, "refs/heads/feature"));
    }
}
