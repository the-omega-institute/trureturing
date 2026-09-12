using System.Text;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Fact]
    public void DepositAfterStatePinRevocationRefreezesAndCoversInOneMakeInvocation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.WriteActiveFreeze();
        fixture.CommitAll("frozen baseline");
        var historyBefore = fixture.LedgerState();
        var pinBefore = fixture.StatePinContents();
        fixture.RevokeStatePin();
        fixture.ChangeFormalization();
        Assert.False(fixture.StatePinExists());
        Assert.Equal(historyBefore, fixture.LedgerState());

        var result = fixture.Run("deposit", useCanonicalFrozenQuery: true, throughMake: true);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.True(fixture.StatePinExists());
        Assert.NotEqual(pinBefore, fixture.StatePinContents());
        Assert.Equal(1, fixture.FreezeCount());
        Assert.NotEqual(historyBefore, fixture.LedgerState());
        Assert.Equal(
            [
                "make:lean-report", "dotnet:deposit-header-check", "make:emit",
                "dotnet:ledger-frozen", "dotnet:ledger-align", "dotnet:ledger-frozen",
                "dotnet:cover-atom", "make:emit",
            ],
            fixture.CallKinds());
        Assert.Contains("coverage: true", fixture.BackfillContents(), StringComparison.Ordinal);
        Assert.Equal("emission: covered\n", fixture.EmissionContents());
        Assert.DoesNotContain("module-already-frozen", Diagnostics(result), StringComparison.Ordinal);
    }

    [Fact]
    public void DepositWithUnchangedStatePinSkipsFreezeAndCovers()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.WriteActiveFreeze();
        fixture.CommitAll("frozen baseline");
        var historyBefore = fixture.LedgerState();
        var pinBefore = fixture.StatePinContents();

        var result = fixture.Run("deposit", useCanonicalFrozenQuery: true, throughMake: true);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(historyBefore, fixture.LedgerState());
        Assert.Equal(pinBefore, fixture.StatePinContents());
        Assert.DoesNotContain("dotnet:ledger-align", fixture.CallKinds());
        Assert.Contains("module-already-frozen", Diagnostics(result), StringComparison.Ordinal);
        Assert.Contains("coverage: true", fixture.BackfillContents(), StringComparison.Ordinal);
    }

    // This case previously returned 0 and skipped the already-frozen target.
    // It now returns 2 without invoking ledger-align because the canonical reader
    // validates every frozen-ledger shard before resolving the target.
    [Fact]
    public void DepositFailsClosedWhenAnUnrelatedFrozenLedgerShardIsMalformed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.WriteActiveFreezeForCurrentModule();
        fixture.AddUnrelatedMalformedLedgerShard();

        var result = fixture.Run("deposit", useCanonicalFrozenQuery: true);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(
            "LEDGER_FROZEN_INVALID",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "module-already-frozen",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet:ledger-align", fixture.CallKinds());
    }

}
