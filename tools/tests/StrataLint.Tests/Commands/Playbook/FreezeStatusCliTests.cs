using System.Text;

namespace StrataLint.Tests;

public sealed class FreezeStatusCliTests
{
    private const string TargetPath = "D5/S0/Carrier/Probe.lean";

    [Fact]
    public void ActiveFrozenPathReturnsFrozenExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new DepositCoverWorkflowScriptTests.TransactionFixture();
        fixture.WriteActiveFreezeForCurrentModule();

        var result = fixture.RunFreezeStatus(TargetPath);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal($"FROZEN path={TargetPath}\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Empty(result.StandardError);
    }

    [Fact]
    public void AbsentFrozenPathReturnsDistinctNotFrozenExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new DepositCoverWorkflowScriptTests.TransactionFixture();

        var result = fixture.RunFreezeStatus(TargetPath);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal($"NOT_FROZEN path={TargetPath}\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Empty(result.StandardError);
    }

    [Fact]
    public void MissingFrozenLedgerReturnsUnavailableRatherThanNotFrozen()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new DepositCoverWorkflowScriptTests.TransactionFixture();
        fixture.RemoveFrozenLedger();

        var result = fixture.RunFreezeStatus(TargetPath);

        Assert.Equal(2, result.ExitCode);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.Empty(result.StandardOutput);
        Assert.Contains("FREEZE_STATUS_UNAVAILABLE", error, StringComparison.Ordinal);
        Assert.DoesNotContain("NOT_FROZEN", error, StringComparison.Ordinal);
    }
}
