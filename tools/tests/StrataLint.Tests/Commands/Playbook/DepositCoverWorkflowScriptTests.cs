using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Fact]
    public void DepositBuildsEmitsFreezesCoversAndReemitsWithoutCommitting()
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
                "make:lean-report",
                "dotnet:deposit-header-check",
                "make:emit",
                "dotnet:ledger-frozen",
                "dotnet:ledger-align",
                "dotnet:ledger-frozen",
                "dotnet:cover-atom",
                "make:emit",
            ],
            fixture.CallKinds());
        Assert.Contains("coverage: true", fixture.BackfillContents(), StringComparison.Ordinal);
        Assert.Equal("emission: covered\n", fixture.EmissionContents());
    }

    [Fact]
    public void DepositReplaySkipsExistingFreezeAndCoverageAndReemits()
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
                "make:lean-report",
                "dotnet:deposit-header-check",
                "make:emit",
                "dotnet:ledger-frozen",
                "dotnet:cover-atom",
                "make:emit",
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
                "make:lean-report",
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
        Assert.Contains("\n    if cover_row; then\n", depositCase, StringComparison.Ordinal);
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

    [Fact]
    public void DepositFailsClosedWhenLeanReportRemainsStale()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run("deposit", staleReport: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains("STALE_LEAN_REPORT", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(
            ["make:lean-report", "dotnet:deposit-header-check", "make:emit"],
            fixture.CallKinds());
        Assert.Equal(0, fixture.FreezeCount());
    }

    [Fact]
    public void CoverWritesEdgeAndReemitsWithoutCommitting()
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
                "make:lean-report",
                "dotnet:cover-atom",
                "make:emit",
            ],
            fixture.CallKinds());
        Assert.Contains("coverage: true", fixture.BackfillContents(), StringComparison.Ordinal);
        Assert.Equal("emission: covered\n", fixture.EmissionContents());
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
        Assert.Equal(["make:lean-report", "dotnet:cover-atom"], fixture.CallKinds());
        Assert.NotEmpty(fixture.Status());
    }

    private static string Diagnostics(ProcessOutput result) =>
        "stdout:\n" + Encoding.UTF8.GetString(result.StandardOutput)
        + "\nstderr:\n" + Encoding.UTF8.GetString(result.StandardError);

}
