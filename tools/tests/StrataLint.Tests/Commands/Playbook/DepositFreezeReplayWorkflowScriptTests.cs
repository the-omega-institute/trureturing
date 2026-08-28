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
    public void DepositSkipsAppendWhenSchemaV4FreezeUsesDescriptorSelector()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.WriteActiveSchemaV4FreezeForCurrentModule();

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
    public void DepositAfterReattestedNodeRevocationAppendsANewFreeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.WriteFreezeThenReattest(revokeReattestedNode: true);

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(1, fixture.CallKinds().Count(call => call == "dotnet:ledger-append"));
        Assert.Equal(2, fixture.FreezeCount());
    }

    [Fact]
    public void DepositSkipsAppendWhenTargetModuleWasReattested()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.WriteFreezeThenReattest(revokeReattestedNode: false);

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

    internal sealed partial class TransactionFixture
    {
        internal void WriteActiveFreezeForCurrentModule() => WriteActiveFreeze(
            "git-sha1:" + Git("hash-object", "--", LeanPath).Trim());

        internal void WriteActiveSchemaV4FreezeForCurrentModule()
        {
            var descriptorBlobOid = "git-sha1:" + Git("hash-object", "--", LeanPath).Trim();
            var freeze = JsonSerializer.Serialize(new
            {
                event_type = "Freeze",
                payload = new
                {
                    case_id = "active-frozen/schema-v4-probe",
                    frozen_node_id =
                        "sha256:5555555555555555555555555555555555555555555555555555555555555555",
                    input = new
                    {
                        descriptor_blob_oid = descriptorBlobOid,
                        descriptor_selector = LeanPath,
                    },
                },
                schema_version = 4,
            });
            WriteLedger(freeze);
        }

        internal void WriteFreezeThenReattest(bool revokeReattestedNode)
        {
            const string caseId = "active-frozen/reattested-probe";
            const string freezeEventHash =
                "sha256:6666666666666666666666666666666666666666666666666666666666666666";
            const string reattestEventHash =
                "sha256:9999999999999999999999999999999999999999999999999999999999999999";
            const string frozenNodeId =
                "sha256:7777777777777777777777777777777777777777777777777777777777777777";
            const string reattestedNodeId =
                "sha256:8888888888888888888888888888888888888888888888888888888888888888";
            var descriptorBlobOid = "git-sha1:" + Git("hash-object", "--", LeanPath).Trim();
            var freeze = JsonSerializer.Serialize(new
            {
                event_hash = freezeEventHash,
                event_type = "Freeze",
                payload = new
                {
                    case_id = caseId,
                    frozen_node_id = frozenNodeId,
                    input = new
                    {
                        descriptor_blob_oid = descriptorBlobOid,
                        descriptor_selector = LeanPath,
                    },
                },
            });
            var reattest = JsonSerializer.Serialize(new
            {
                event_hash = reattestEventHash,
                event_type = "Reattest",
                payload = new
                {
                    case_id = caseId,
                    frozen_node_id = reattestedNodeId,
                    input = new
                    {
                        descriptor_blob_oid = descriptorBlobOid,
                        descriptor_selector = LeanPath,
                    },
                    previous_attestation_event_hash = freezeEventHash,
                },
            });
            if (!revokeReattestedNode)
            {
                WriteLedger(freeze, reattest);
                return;
            }

            var revoke = JsonSerializer.Serialize(new
            {
                event_type = "Revoke",
                payload = new
                {
                    affected_case_ids = new[] { caseId },
                    affected_frozen_node_ids = new[] { reattestedNodeId },
                },
            });
            WriteLedger(freeze, reattest, revoke);
        }

        internal void AddUnrelatedMalformedLedgerShard() => WriteFile(
            LedgerPath + "/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json",
            "{\"event_type\":\"Freeze\",\"payload\":{\"node_path\":\"D5/S4/Unrelated.lean\"\n");

    }
}
