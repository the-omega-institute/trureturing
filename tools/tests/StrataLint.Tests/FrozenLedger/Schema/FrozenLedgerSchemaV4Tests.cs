using System.Collections.Immutable;
using System.Reflection;
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

    [Fact]
    public void CurrentRuntimePayloadContractsOmitRetiredWriterFields()
    {
        var freezeFields = typeof(FrozenFreezePayload)
            .GetProperties(BindingFlags.Instance | BindingFlags.Public | BindingFlags.DeclaredOnly)
            .Select(static property => property.Name)
            .ToHashSet(StringComparer.Ordinal);
        var reattestFields = typeof(FrozenReattestPayload)
            .GetProperties(BindingFlags.Instance | BindingFlags.Public | BindingFlags.DeclaredOnly)
            .Select(static property => property.Name)
            .ToHashSet(StringComparer.Ordinal);

        Assert.Empty(freezeFields.Intersect(
        [
            "CaseClass",
            "Evaluation",
            "Expected",
            "InputFingerprint",
            "NodePath",
            "SemanticReceipt",
            "TruthState",
        ]));
        Assert.Empty(reattestFields.Intersect(["InputFingerprint", "SemanticReceipt"]));
    }

    [Fact]
    public void CurrentRevokeWriterOmitsEventLocalRootAndExpectedAddressAliases()
    {
        var root = FrozenNodeId.Create(Sha256("root"));
        var evidence = new RevocationEvidence.ContentAddressMismatch(
            root,
            root.Value,
            Sha256("actual"),
            GitOid('a'),
            Sha256("receipt"));
        var payload = FrozenLedgerCanonicalWriter.RevokeElement(new FrozenRevokePayload(
            ImmutableArray.Create("active-frozen/root"),
            ImmutableArray.Create(root),
            Sha256("closure"),
            ImmutableArray.Create<RevocationEvidence>(evidence),
            Sha256("graph"),
            ImmutableArray.Create("active-frozen/root")));

        Assert.False(payload.TryGetProperty("root_frozen_node_ids", out _));
        var encodedEvidence = Assert.Single(payload.GetProperty("evidence").EnumerateArray().ToArray());
        Assert.False(encodedEvidence.TryGetProperty("expected_sha256", out _));
        Assert.Equal(root.Value, encodedEvidence.GetProperty("root_frozen_node_id").GetString());
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
