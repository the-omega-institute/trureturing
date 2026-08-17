using System.Text;
using System.Text.Json;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Fact]
    public void DepositSkipsAppendWhenTargetModuleHasAnActiveFreeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.WriteActiveFreezeForCurrentModule();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains(
            "module-already-frozen",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
        Assert.Equal(1, fixture.FreezeCount());
    }

    [Fact]
    public void DepositDoesNotReplayAnUnrelatedMalformedFrozenLedgerShard()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.WriteActiveFreezeForCurrentModule();
        fixture.AddUnrelatedMalformedLedgerShard();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains(
            "module-already-frozen",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
    }

    [Fact]
    public void DepositFollowsASupersedeChainToTheTargetFreeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.WriteActiveSupersedeChain();

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains(
            "module-already-frozen",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
        Assert.Equal(1, fixture.FreezeCount());
    }

    internal sealed partial class TransactionFixture
    {
        internal void WriteActiveFreezeForCurrentModule() => WriteActiveFreeze(
            "git-sha1:" + Git("hash-object", "--", LeanPath).Trim());

        internal void AddUnrelatedMalformedLedgerShard() => WriteFile(
            LedgerPath + "/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json",
            "{\"event_type\":\"Freeze\",\"payload\":{\"node_path\":\"D5/S4/Unrelated.lean\"\n");

        internal void WriteActiveSupersedeChain()
        {
            const string caseId = "active-frozen/superseded-probe";
            const string freezeHash =
                "sha256:1111111111111111111111111111111111111111111111111111111111111111";
            const string initialFrozenNodeId =
                "sha256:2222222222222222222222222222222222222222222222222222222222222222";
            const string currentFrozenNodeId =
                "sha256:3333333333333333333333333333333333333333333333333333333333333333";
            var currentDescriptorBlobOid = "git-sha1:" + Git("hash-object", "--", LeanPath).Trim();
            var freeze = JsonSerializer.Serialize(new
            {
                event_hash = freezeHash,
                event_type = "Freeze",
                payload = new
                {
                    case_id = caseId,
                    frozen_node_id = initialFrozenNodeId,
                    input = new
                    {
                        descriptor_blob_oid =
                            "git-sha1:0000000000000000000000000000000000000000",
                    },
                    node_path = LeanPath,
                },
            });
            var supersede = JsonSerializer.Serialize(new
            {
                event_hash =
                    "sha256:4444444444444444444444444444444444444444444444444444444444444444",
                event_type = "Supersede",
                payload = new
                {
                    case_id = caseId,
                    frozen_node_id = currentFrozenNodeId,
                    input = new { descriptor_blob_oid = currentDescriptorBlobOid },
                    previous_attestation_event_hash = freezeHash,
                },
            });
            WriteLedger(
                (initialFrozenNodeId["sha256:".Length..] + ".json", freeze),
                ("4444444444444444444444444444444444444444444444444444444444444444.json",
                    supersede));
        }
    }
}
