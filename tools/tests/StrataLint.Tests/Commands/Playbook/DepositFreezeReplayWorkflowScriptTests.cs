using static StrataLint.TestSupport.TransactionFixture;

namespace StrataLint.Tests;

public sealed class DepositFreezeReplayWorkflowScriptTests
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

        var result = fixture.Run("deposit", realCliPath: Path.Combine(Path.GetDirectoryName(typeof(StrataLint.Cli.Program).Assembly.Location)!, "StrataLint"), throughMake: true);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.True(fixture.StatePinExists());
        Assert.NotEqual(pinBefore, fixture.StatePinContents());
        Assert.Equal(1, fixture.FreezeCount());
        Assert.NotEqual(historyBefore, fixture.LedgerState());
        Assert.Equal(
            [
                "make:lean-report-scoped", "dotnet:deposit-header-check", "make:emit",
                "dotnet:ledger-frozen", "dotnet:ledger-align", "dotnet:ledger-frozen",
                "dotnet:cover-atom --lean-inputs", "dotnet:cover-atom",
            ],
            fixture.CallKinds());
        Assert.Contains("coverage: true", fixture.BackfillContents(), StringComparison.Ordinal);
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

        var result = fixture.Run("deposit", realCliPath: Path.Combine(Path.GetDirectoryName(typeof(StrataLint.Cli.Program).Assembly.Location)!, "StrataLint"), throughMake: true);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(historyBefore, fixture.LedgerState());
        Assert.Equal(pinBefore, fixture.StatePinContents());
        Assert.DoesNotContain("dotnet:ledger-align", fixture.CallKinds());
        Assert.Contains("module-already-frozen", Diagnostics(result), StringComparison.Ordinal);
        Assert.Contains("coverage: true", fixture.BackfillContents(), StringComparison.Ordinal);
    }

    [Fact]
    public void DepositWithExistingStatePinIgnoresAnUnrelatedMalformedFrozenLedgerShard()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.WriteActiveFreezeForCurrentModule();
        fixture.AddUnrelatedMalformedLedgerShard();
        var historyBefore = fixture.LedgerState();
        var pinBefore = fixture.StatePinContents();

        var result = fixture.Run("deposit", realCliPath: Path.Combine(Path.GetDirectoryName(typeof(StrataLint.Cli.Program).Assembly.Location)!, "StrataLint"));

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(historyBefore, fixture.LedgerState());
        Assert.Equal(pinBefore, fixture.StatePinContents());
        Assert.Equal(
            [
                "make:lean-report-scoped", "dotnet:deposit-header-check", "make:emit",
                "dotnet:ledger-frozen", "dotnet:cover-atom --lean-inputs", "dotnet:cover-atom",
            ],
            fixture.CallKinds());
        Assert.Contains("module-already-frozen", Diagnostics(result), StringComparison.Ordinal);
        Assert.DoesNotContain("LEDGER_FROZEN_INVALID", Diagnostics(result), StringComparison.Ordinal);
        Assert.Contains("coverage: true", fixture.BackfillContents(), StringComparison.Ordinal);
    }

}
