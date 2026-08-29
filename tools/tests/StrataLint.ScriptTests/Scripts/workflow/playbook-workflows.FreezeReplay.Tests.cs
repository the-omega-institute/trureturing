using System.Text;
using System.Text.Json;

namespace StrataLint.ScriptTests;

public sealed partial class PlaybookWorkflowsTests
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
    public void DepositAfterMultiCaseRevocationAppendsANewFreeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        fixture.WriteMultiCaseRevocation(includesTargetCase: true);

        var result = fixture.Run("deposit");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.DoesNotContain(
            "PLAYBOOK_INVALID",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.Equal(1, fixture.CallKinds().Count(call => call == "dotnet:ledger-append"));
        Assert.Equal(2, fixture.FreezeCount());
    }

    [Fact]
    public void DepositSkipsAppendWhenMultiCaseRevocationDoesNotIncludeTarget()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.WriteMultiCaseRevocation(includesTargetCase: false);

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

        internal void WriteMultiCaseRevocation(bool includesTargetCase)
        {
            const string targetCaseId = "active-frozen/multi-case-target";
            const string unrelatedCaseId = "active-frozen/multi-case-unrelated";
            const string secondUnrelatedCaseId = "active-frozen/multi-case-second-unrelated";
            const string targetFrozenNodeId =
                "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
            const string unrelatedFrozenNodeId =
                "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
            const string secondUnrelatedFrozenNodeId =
                "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
            var descriptorBlobOid = "git-sha1:" + Git("hash-object", "--", LeanPath).Trim();

            string Freeze(string caseId, string frozenNodeId, string descriptorSelector) =>
                JsonSerializer.Serialize(new
                {
                    event_type = "Freeze",
                    payload = new
                    {
                        case_id = caseId,
                        frozen_node_id = frozenNodeId,
                        input = new
                        {
                            descriptor_blob_oid = descriptorBlobOid,
                            descriptor_selector = descriptorSelector,
                        },
                    },
                });

            var events = new List<string>
            {
                Freeze(targetCaseId, targetFrozenNodeId, LeanPath),
                Freeze(unrelatedCaseId, unrelatedFrozenNodeId, "D5/S4/Unrelated.lean"),
            };
            string[] affectedCaseIds;
            string[] affectedFrozenNodeIds;
            if (includesTargetCase)
            {
                affectedCaseIds = [targetCaseId, unrelatedCaseId];
                affectedFrozenNodeIds = [targetFrozenNodeId, unrelatedFrozenNodeId];
            }
            else
            {
                events.Add(Freeze(
                    secondUnrelatedCaseId,
                    secondUnrelatedFrozenNodeId,
                    "D5/S4/SecondUnrelated.lean"));
                affectedCaseIds = [unrelatedCaseId, secondUnrelatedCaseId];
                affectedFrozenNodeIds = [unrelatedFrozenNodeId, secondUnrelatedFrozenNodeId];
            }

            events.Add(JsonSerializer.Serialize(new
            {
                event_type = "Revoke",
                payload = new
                {
                    affected_case_ids = affectedCaseIds,
                    affected_frozen_node_ids = affectedFrozenNodeIds,
                },
            }));
            WriteLedger(events.ToArray());
        }

        internal void AddUnrelatedMalformedLedgerShard() => WriteFile(
            LedgerPath + "/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json",
            "{\"event_type\":\"Freeze\",\"payload\":{\"node_path\":\"D5/S4/Unrelated.lean\"\n");

    }
}
