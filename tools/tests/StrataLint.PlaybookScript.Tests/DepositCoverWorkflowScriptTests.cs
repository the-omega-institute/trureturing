using static StrataLint.TestSupport.TransactionFixture;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.PlaybookScript.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Theory]
    [InlineData(false, "none")]
    [InlineData(false, TransactionFixture.AtomId)]
    [InlineData(false, "")]
    [InlineData(true, "none")]
    [InlineData(true, TransactionFixture.AtomId)]
    [InlineData(true, "")]
    public void DepositUncoveredRejectsAtomIdAndFreezesNothing(bool throughMake, string atomId)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run("deposit-uncovered", atomId: atomId, throughMake: throughMake);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(0, fixture.FreezeCount());
        Assert.Empty(fixture.CallKinds());
        Assert.Contains("usage: playbook-workflows.sh", Diagnostics(result), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DepositUncoveredFreezesExactlyOnceWithoutCovering(bool throughMake)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var commitsBefore = fixture.CommitCount();
        var backfillBefore = fixture.BackfillContents();

        var result = fixture.Run("deposit-uncovered", atomId: null, throughMake: throughMake);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(1, fixture.FreezeCount());
        Assert.Equal(commitsBefore, fixture.CommitCount());
        Assert.Equal(backfillBefore, fixture.BackfillContents());
        Assert.Equal(
            [
                "make:lean-report-scoped",
                "dotnet:deposit-header-check",
                "make:emit",
                "dotnet:ledger-frozen",
                "dotnet:ledger-align",
                "dotnet:ledger-frozen",
            ],
            fixture.CallKinds());
        Assert.Contains(
            $"dotnet:deposit-header-check --target {TransactionFixture.LeanPath} --protected-base {fixture.HeadRevision()}",
            fixture.Calls());
        Assert.Contains(
            $"PLAYBOOK_DEPOSIT_FROZEN gid={TransactionFixture.Gid}",
            Diagnostics(result), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("", "HEAD", "GID does not resolve")]
    [InlineData("D5/S0/Carrier/Probe", "HEAD", "GID does not resolve")]
    [InlineData("D5/S2/Missing.missing", "HEAD", "GID does not resolve")]
    [InlineData(TransactionFixture.Gid, "missing-base", "base does not resolve")]
    public void DepositUncoveredRejectsInvalidModuleOrBaseBeforeFreeze(string gid, string baseRevision, string diagnostic)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();

        var result = fixture.Run("deposit-uncovered", gid, atomId: null, baseRevision: baseRevision);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(0, fixture.FreezeCount());
        Assert.Empty(fixture.CallKinds());
        Assert.Contains(diagnostic, Diagnostics(result), StringComparison.Ordinal);
    }

    [Fact]
    public void DepositForUnregisteredModuleWritesItsState()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(1, fixture.CallKinds().Count(call => call == "dotnet:ledger-align"));
        Assert.Equal(1, fixture.FreezeCount());
    }

    [Fact]
    public void DepositSkipsFreezeWhenTheModulePathIsAlreadyActive()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.WriteActiveFreeze();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.DoesNotContain("dotnet:ledger-align", fixture.CallKinds());
        Assert.Equal(1, fixture.FreezeCount());
    }

    [Fact]
    public void DepositPropagatesLedgerFrozenInfrastructureFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.FailFrozenQuery();

        var result = fixture.Run("deposit");

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("LEDGER_FROZEN_INVALID", Encoding.UTF8.GetString(result.StandardError));
        Assert.DoesNotContain("dotnet:ledger-align", fixture.CallKinds());
    }

    [Fact]
    public void DepositRejectsFrozenQueryLauncherFailureBeforeWriting()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.FailFrozenLauncher();

        var result = fixture.Run("deposit-uncovered", atomId: null);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("synthetic launcher failure", Encoding.UTF8.GetString(result.StandardError));
        Assert.DoesNotContain("dotnet:ledger-align", fixture.CallKinds());
        Assert.Equal(0, fixture.FreezeCount());
    }

    [Theory]
    [InlineData("deposit")]
    [InlineData("deposit-uncovered")]
    public void DepositFailsClosedWhenLeanReportRemainsStale(string command)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run(command, atomId: null, staleReport: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("STALE_LEAN_REPORT", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(
            ["make:lean-report-scoped", "dotnet:deposit-header-check", "make:emit"],
            fixture.CallKinds());
        Assert.Equal(0, fixture.FreezeCount());
    }

}
