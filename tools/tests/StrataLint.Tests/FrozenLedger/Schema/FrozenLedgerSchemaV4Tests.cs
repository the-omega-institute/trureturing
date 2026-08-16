using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class FrozenLedgerSchemaV4Tests
{
    [Fact]
    public void CurrentAttestationWritersOmitProjectionAliasesAndUseTheEventHashAddress()
    {
        var catalog = BuildCatalog(Module("A"));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(Load(baselineBytes), catalog)).Capability;
        var freezePayload = Payload(Lines(baselineBytes)[1]);
        var freezeEvent = FrozenLedgerCanonicalWriter.WriteDagEvent("Freeze", freezePayload);
        var reattestedBytes = FrozenLedgerGenerator.AppendReattestation(
            baseline,
            Assert.Single(baseline.ActiveEntries).Key,
            Assert.Single(baseline.ActiveEntries).Value.Payload.Input);
        var reattestPayload = Payload(Lines(reattestedBytes)[^1]);

        Assert.Equal(4, FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion);
        AssertProjectionAliasesAbsent(freezePayload, includesNodePath: true);
        AssertProjectionAliasesAbsent(reattestPayload, includesNodePath: false);
        Assert.Equal(
            freezeEvent.Hash,
            FrozenLedgerCanonicalWriter.EventIdentity("Freeze", freezePayload, freezeEvent.Hash));
    }

    [Fact]
    public void CurrentFreezeWriterOmitsTheConstantOnlyVerdictFamily()
    {
        var catalog = BuildCatalog(Module("A"));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var payload = Payload(Lines(bytes)[1]);

        foreach (var field in new[] { "case_class", "evaluation", "expected", "truth_state" })
        {
            Assert.False(payload.TryGetProperty(field, out _), $"current Freeze emitted {field}");
        }
    }

    private static void AssertProjectionAliasesAbsent(JsonElement payload, bool includesNodePath)
    {
        Assert.False(payload.TryGetProperty("input_fingerprint", out _));
        Assert.False(payload.TryGetProperty("semantic_receipt", out _));
        if (includesNodePath)
        {
            Assert.False(payload.TryGetProperty("node_path", out _));
        }
    }

    private static JsonElement Payload(byte[] line)
    {
        using var document = JsonDocument.Parse(line.AsMemory(0, line.Length - 1));
        return document.RootElement.GetProperty("payload").Clone();
    }

    private static FrozenLedgerSyntax Load(IEnumerable<byte> bytes)
    {
        var loaded = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes.ToArray()));
        return loaded.Syntax;
    }
}
