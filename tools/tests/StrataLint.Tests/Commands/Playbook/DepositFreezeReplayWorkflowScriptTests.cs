using System.Text;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
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

    internal sealed partial class TransactionFixture
    {
        internal void WriteActiveFreezeForCurrentModule() => WriteActiveFreeze();

        internal void AddUnrelatedMalformedLedgerShard() => WriteFile(
            LedgerPath + "/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json",
            "{\"event_type\":\"Freeze\",\"payload\":{\"node_path\":\"D5/S4/Unrelated.lean\"\n");
    }
}
