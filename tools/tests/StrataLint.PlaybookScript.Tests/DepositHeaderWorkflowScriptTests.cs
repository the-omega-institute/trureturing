using static StrataLint.TestSupport.TransactionFixture;

namespace StrataLint.PlaybookScript.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{

    [Theory]
    [InlineData("deposit")]
    [InlineData("deposit-uncovered")]
    public void DepositRejectsSevenLineWrappedDigestBeforeFreezeAndWritesNothing(string command)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalizationToSevenLineWrappedDigest();
        var commitsBefore = fixture.CommitCount();
        var blueprintBefore = fixture.BlueprintState();

        var result = fixture.Run(command, atomId: command == "deposit" ? TransactionFixture.AtomId : null, rejectDepositHeader: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            $"SL-012 {TransactionFixture.LeanPath}: {CanonicalHeaderFinding}",
            Diagnostics(result),
            StringComparison.Ordinal);
        Assert.Equal(commitsBefore, fixture.CommitCount());
        Assert.Equal(0, fixture.FreezeCount());
        Assert.Equal(blueprintBefore, fixture.BlueprintState());
        Assert.DoesNotContain("make:emit", fixture.CallKinds());
        Assert.DoesNotContain("dotnet:ledger-align", fixture.CallKinds());
    }

    [Theory]
    [InlineData("deposit")]
    [InlineData("deposit-uncovered")]
    public void DepositRejectsSevenLineWrappedDigestWithExistingFreezeBeforeEmission(string command)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalizationToSevenLineWrappedDigest();
        fixture.WriteActiveFreeze();
        var commitsBefore = fixture.CommitCount();
        var blueprintBefore = fixture.BlueprintState();
        var ledgerBefore = fixture.LedgerState();

        var result = fixture.Run(command, atomId: command == "deposit" ? TransactionFixture.AtomId : null, rejectDepositHeader: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            $"SL-012 {TransactionFixture.LeanPath}: {CanonicalHeaderFinding}",
            Diagnostics(result),
            StringComparison.Ordinal);
        Assert.Equal(commitsBefore, fixture.CommitCount());
        Assert.Equal(blueprintBefore, fixture.BlueprintState());
        Assert.Equal(ledgerBefore, fixture.LedgerState());
        Assert.Equal(
            ["make:lean-report", "dotnet:deposit-header-check"],
            fixture.CallKinds());
        Assert.DoesNotContain("make:emit", fixture.CallKinds());
        Assert.DoesNotContain("dotnet:ledger-align", fixture.CallKinds());
    }
}
