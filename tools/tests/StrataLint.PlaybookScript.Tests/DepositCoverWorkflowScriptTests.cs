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
        Assert.Contains("ATOM_ID is not accepted", Diagnostics(result), StringComparison.Ordinal);
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
            $"PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED gid={TransactionFixture.Gid} reason=NO_ATOM",
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
    public void DepositRefusesAnAtomIdThatResolvesToNoLedgerEntryAndFreezesNothing()
    {
        // 形状合法但不存在的 atom id 必须在冻结前被拒绝。
        // 冻结不可逆,故同时断言非零退出与零次冻结。
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run("deposit", atomId: "none");

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(0, fixture.FreezeCount());
        Assert.Contains("atom not found in the digestion ledger", Diagnostics(result), StringComparison.Ordinal);
    }

    [Fact]
    public void DepositBuildsEmitsFreezesAndCoversWithoutCommitting()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var before = fixture.CommitCount();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(before, fixture.CommitCount());
        Assert.Equal(1, fixture.FreezeCount());
        Assert.Equal(0, fixture.FreezeProbeCount());
        Assert.NotEmpty(fixture.Status());
        Assert.Equal(
            [
                "make:lean-report-scoped",
                "dotnet:deposit-header-check",
                "make:emit",
                "dotnet:ledger-frozen",
                "dotnet:ledger-align",
                "dotnet:ledger-frozen",
                "dotnet:cover-atom",
            ],
            fixture.CallKinds());
        Assert.Contains("coverage: true", fixture.BackfillContents(), StringComparison.Ordinal);
    }

    [Fact]
    public void DepositReplaySkipsExistingFreezeAndCoverage()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.WriteActiveFreeze();
        File.WriteAllText(
            Path.Combine(fixture.Root, TransactionFixture.BackfillPath),
            $"atom_id: {TransactionFixture.AtomId}\ncoverage: true\naligned: false\n");
        var ledgerBefore = fixture.LedgerState();
        var backfillBefore = fixture.BackfillContents();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(ledgerBefore, fixture.LedgerState());
        Assert.Equal(backfillBefore, fixture.BackfillContents());
        Assert.Equal(
            [
                "make:lean-report-scoped",
                "dotnet:deposit-header-check",
                "make:emit",
                "dotnet:ledger-frozen",
                "dotnet:cover-atom",
            ],
            fixture.CallKinds());
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("PLAYBOOK_SKIP command=deposit detail=module-already-frozen", error);
        Assert.Contains("PLAYBOOK_SKIP command=cover detail=coverage-already-applied", error);
    }

    [Fact]
    public void DepositCoverFailureKeepsFreezeAndReportsFrozenUncovered()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run("deposit", coverDispositionFailure: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(1, fixture.FreezeCount());
        Assert.Equal(
            [
                "make:lean-report-scoped",
                "dotnet:deposit-header-check",
                "make:emit",
                "dotnet:ledger-frozen",
                "dotnet:ledger-align",
                "dotnet:ledger-frozen",
                "dotnet:cover-atom",
            ],
            fixture.CallKinds());
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("COVER_INVALID synthetic disposition", error, StringComparison.Ordinal);
        Assert.Contains(
            $"PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED atom_id={TransactionFixture.AtomId} "
                + $"gid={TransactionFixture.Gid} reason=COVER_INVALID synthetic disposition",
            error,
            StringComparison.Ordinal);
        Assert.Contains("cover_disposition:", fixture.BackfillContents(), StringComparison.Ordinal);
        Assert.DoesNotContain("coverage: true", fixture.BackfillContents(), StringComparison.Ordinal);
    }

    [Fact]
    public void DepositDelegatesCoverageWritingExclusivelyToCoverAtom()
    {
        var script = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/workflow/playbook-workflows.sh"));
        var depositStart = script.IndexOf("  deposit)", StringComparison.Ordinal);
        var coverStart = script.IndexOf("  cover)", depositStart, StringComparison.Ordinal);

        Assert.True(depositStart >= 0 && coverStart > depositStart);
        var depositCase = script[depositStart..coverStart];
        Assert.Contains("\n    cover_row || {\n", depositCase, StringComparison.Ordinal);
        Assert.DoesNotContain("coverage_gids", script, StringComparison.Ordinal);
        Assert.Single(Regex.Matches(script, @"run_cli\s+cover-atom\b").Cast<Match>());
    }

    [Fact]
    public void DepositAfterSnapshotRevocationAppendsANewFreeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.WriteRevokedSnapshot();

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

    [Theory]
    [InlineData("deposit")]
    [InlineData("deposit-uncovered")]
    public void DepositFailsClosedWhenLeanReportRemainsStale(string command)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run(command, atomId: command == "deposit" ? TransactionFixture.AtomId : null, staleReport: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("STALE_LEAN_REPORT", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(
            ["make:lean-report-scoped", "dotnet:deposit-header-check", "make:emit"],
            fixture.CallKinds());
        Assert.Equal(0, fixture.FreezeCount());
    }

    [Fact]
    public void CoverWritesEdgeWithoutEmittingOrCommitting()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var deposit = fixture.Run("deposit");
        Assert.True(deposit.ExitCode == 0, Diagnostics(deposit));
        fixture.ClearCalls();
        var before = fixture.CommitCount();

        var result = fixture.Run("cover");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(before, fixture.CommitCount());
        Assert.Equal(
            [
                "make:lean-report-scoped",
                "dotnet:cover-atom",
            ],
            fixture.CallKinds());
        Assert.Contains("coverage: true", fixture.BackfillContents(), StringComparison.Ordinal);
        Assert.NotEmpty(fixture.Status());
    }

    [Fact]
    public void FailedCoverLeavesDispositionUncommittedBeforeReturningFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        var before = fixture.CommitCount();

        var result = fixture.Run("cover", coverDispositionFailure: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "COVER_INVALID synthetic disposition",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.Equal(before, fixture.CommitCount());
        Assert.Contains("cover_disposition:", fixture.BackfillContents(), StringComparison.Ordinal);
        Assert.Equal(["make:lean-report-scoped", "dotnet:cover-atom"], fixture.CallKinds());
        Assert.NotEmpty(fixture.Status());
    }

}
