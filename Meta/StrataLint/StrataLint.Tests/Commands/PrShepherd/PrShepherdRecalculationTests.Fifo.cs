namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void DerivedQueueProcessesOnlyTheLowestPullRequestPerSweep()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.Run(dryRun: true, twoDerivedPrRows: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            1,
            result.Log.Split("DRYRUN #1 RECALCULATE", StringSplitOptions.None).Length - 1);
        Assert.DoesNotContain("DRYRUN #2 RECALCULATE", result.Log, StringComparison.Ordinal);
        Assert.Contains("FIFO LEASE acquired pr=#1 acquired_at=", result.Log, StringComparison.Ordinal);
        Assert.Contains("SWEEP #2 derived FIFO waiting head=#1", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void ExpiredDerivedLeaseIsReclaimedBeforeQueueHeadRuns()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var expiredAt = DateTimeOffset.UtcNow.ToUnixTimeSeconds() - 3_600;
        fixture.WriteDerivedLease(99, expiredAt);

        var result = fixture.Run(leaseTtlSeconds: 60);

        Assert.Equal(0, result.ExitCode);
        Assert.NotEqual(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Contains(
            $"FIFO LEASE expired pr=#99 acquired_at={expiredAt}",
            result.Log,
            StringComparison.Ordinal);
        Assert.Contains("FIFO LEASE acquired pr=#1 acquired_at=", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void ActiveDerivedLeaseDefersTheQueueHead()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        var acquiredAt = DateTimeOffset.UtcNow.ToUnixTimeSeconds();
        fixture.WriteDerivedLease(99, acquiredAt);

        var result = fixture.Run(leaseTtlSeconds: 3_600);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Empty(fixture.MutationCalls());
        Assert.Contains(
            $"SWEEP #1 derived FIFO waiting lease_pr=#99 acquired_at={acquiredAt}",
            result.Log,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IncompleteLeaseFromACrashedAcquirerExpires()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        const long expiredAt = 1_700_000_000;
        fixture.WriteIncompleteDerivedLease();
        fixture.UseGnuStatWithMtime(expiredAt);
        fixture.UseFixedClock(expiredAt + 60);

        var result = fixture.Run(leaseTtlSeconds: 60);

        Assert.Equal(0, result.ExitCode);
        Assert.NotEqual(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Contains(
            $"FIFO LEASE expired pr=#unknown acquired_at={expiredAt}",
            result.Log,
            StringComparison.Ordinal);
        Assert.Contains("FIFO LEASE acquired pr=#1 acquired_at=", result.Log, StringComparison.Ordinal);
    }

    [Fact]
    public void ActiveDerivedLeaseDoesNotChangeOrdinaryBehindHandling()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();
        fixture.WriteDerivedLease(99, DateTimeOffset.UtcNow.ToUnixTimeSeconds());

        var result = fixture.Run(
            expiryFingerprint: false,
            leaseTtlSeconds: 3_600,
            derivedPr: false);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            ["gh-api:-X PUT repos/the-omega-institute/trureturing/pulls/1/update-branch"],
            fixture.MutationCalls());
        Assert.Contains(
            "SWEEP #1 BEHIND -> update-branch(本地身份,checks 会触发)",
            result.Log,
            StringComparison.Ordinal);
        Assert.DoesNotContain("derived FIFO waiting", result.Log, StringComparison.Ordinal);
    }
}
