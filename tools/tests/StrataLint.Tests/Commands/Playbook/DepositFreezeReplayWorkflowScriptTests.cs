using System.Text;

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
    public void DepositReportsUnavailableForAnUnrelatedMalformedFrozenLedgerShard()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.WriteActiveFreezeForCurrentModule();
        fixture.AddUnrelatedMalformedLedgerShard();

        var result = fixture.Run("deposit");

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(
            "FREEZE_STATUS_UNAVAILABLE",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
    }

    [Fact]
    public void DepositReportsUnavailableWhenTheFrozenLedgerDirectoryIsMissing()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.RemoveFrozenLedger();

        var result = fixture.Run("deposit");

        var output = Encoding.UTF8.GetString(result.StandardOutput);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("FREEZE_STATUS_UNAVAILABLE", error, StringComparison.Ordinal);
        Assert.DoesNotContain("NOT_FROZEN", output, StringComparison.Ordinal);
        Assert.DoesNotContain("module-already-frozen", error, StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
    }

    [Fact]
    public void DepositPropagatesUnavailableFromThePostAppendFreezeCheck()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run("deposit", removeFrozenLedgerAfterAppend: true);

        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("FREEZE_STATUS_UNAVAILABLE", error, StringComparison.Ordinal);
        Assert.DoesNotContain("did not freeze target module", error, StringComparison.Ordinal);
        Assert.Equal(1, fixture.CallKinds().Count(call => call == "dotnet:ledger-append"));
    }

    internal sealed partial class TransactionFixture
    {
        internal void WriteActiveFreezeForCurrentModule() => WriteActiveFreeze(
            "git-sha1:" + Git("hash-object", "--", LeanPath).Trim());

        internal void WriteActiveSchemaV4FreezeForCurrentModule()
            => WriteActiveFreezeForCurrentModule();

        internal void WriteFreezeThenReattest(bool revokeReattestedNode)
        {
            const string caseId = "active-frozen/reattested-probe";
            const string frozenNodeId =
                "sha256:7777777777777777777777777777777777777777777777777777777777777777";
            const string reattestedNodeId =
                "sha256:8888888888888888888888888888888888888888888888888888888888888888";
            var descriptorBlobOid = "git-sha1:" + Git("hash-object", "--", LeanPath).Trim();
            var freeze = Freeze(caseId, frozenNodeId, descriptorBlobOid, LeanPath);
            var reattest = Reattest(caseId, reattestedNodeId, descriptorBlobOid, LeanPath, 0);
            if (!revokeReattestedNode)
            {
                WriteLedger(freeze, reattest);
                return;
            }

            WriteLedger(freeze, reattest, Revoke([caseId], [reattestedNodeId]));
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

            FrozenFixtureEvent FreezeFor(string caseId, string frozenNodeId, string path) =>
                Freeze(caseId, frozenNodeId, descriptorBlobOid, path);

            var events = new List<FrozenFixtureEvent>
            {
                FreezeFor(targetCaseId, targetFrozenNodeId, LeanPath),
                FreezeFor(unrelatedCaseId, unrelatedFrozenNodeId, "D5/S4/Unrelated.lean"),
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
                events.Add(FreezeFor(
                    secondUnrelatedCaseId,
                    secondUnrelatedFrozenNodeId,
                    "D5/S4/SecondUnrelated.lean"));
                affectedCaseIds = [secondUnrelatedCaseId, unrelatedCaseId];
                affectedFrozenNodeIds = [unrelatedFrozenNodeId, secondUnrelatedFrozenNodeId];
            }

            events.Add(Revoke(affectedCaseIds, affectedFrozenNodeIds));
            WriteLedger(events.ToArray());
        }

        internal void AddUnrelatedMalformedLedgerShard() => WriteFile(
            LedgerPath + "/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json",
            "{\"event_type\":\"Freeze\",\"payload\":{\"node_path\":\"D5/S4/Unrelated.lean\"\n");

        internal void RemoveFrozenLedger() => Directory.Delete(
            Path.Combine(Root, LedgerPath),
            recursive: true);

    }
}
