using System.Collections.Immutable;
using System.Reflection;
using System.Text.Json;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class FrozenLedgerSchemaV5Tests
{
    [Fact]
    public void CurrentFreezeWriterEmitsExactlyTheV5PropositionSnapshotFields()
    {
        var catalog = BuildCatalog(Module("A"));
        var freezePayload = FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(
                Assert.Single(catalog.ClosedNodes)));
        var freezeEvent = FrozenLedgerCanonicalWriter.WriteDagEvent("Freeze", freezePayload);

        Assert.Equal(5, FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion);
        Assert.Equal(
            [
                "declaration_statement_ids",
                "descriptor_selector",
                "prerequisite_frozen_node_ids",
                "statement_id",
            ],
            freezePayload.EnumerateObject()
                .Select(static property => property.Name)
                .Order(StringComparer.Ordinal)
                .ToArray());
        AssertProjectionAliasesAbsent(freezePayload, includesNodePath: true);
        Assert.Equal(
            freezeEvent.Hash,
            FrozenLedgerCanonicalWriter.EventIdentity(freezeEvent.Hash));
    }

    [Fact]
    public void CurrentDagWriterAndCandidateReaderPinSchemaVersionByEventType()
    {
        var payload = JsonSerializer.SerializeToElement(new { });
        var freeze = FrozenLedgerCanonicalWriter.WriteDagEvent("Freeze", payload);

        Assert.Equal(5, SchemaVersion(freeze.Bytes));
        Assert.Throws<ArgumentOutOfRangeException>(() =>
            FrozenLedgerCanonicalWriter.WriteDagEvent("Freeze", payload, 2));

        AssertRejectedByCandidateReader(WithSchemaVersion(freeze.Bytes, 4), "Freeze", 5);
    }

    [Fact]
    public void CurrentCandidateDagReaderRejectsRetiredV1EnvelopeFields()
    {
        var payload = JsonSerializer.SerializeToElement(new { });
        var freeze = FrozenLedgerCanonicalWriter.WriteDagEvent("Freeze", payload);
        using var document = JsonDocument.Parse(freeze.Bytes.AsSpan()[..^1].ToArray());
        var root = System.Text.Json.Nodes.JsonNode.Parse(document.RootElement.GetRawText())!.AsObject();
        root["previous_hash"] = "sha256:" + new string('0', 64);
        root["sequence"] = 1;
        var legacyEnvelope = JsonSerializer.SerializeToElement(root);

        Assert.False(FrozenLedgerCanonicalWriter.ValidateDagEvent(
            legacyEnvelope,
            out _,
            out _,
            out var validationMessage));
        Assert.Contains("unknown, missing, or duplicate fields", validationMessage, StringComparison.Ordinal);
    }

    [Fact]
    public void CurrentCandidateFreezeRejectsHistoricalInputObject()
    {
        var catalog = BuildCatalog(Module("A"));
        var payload = FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(
                Assert.Single(catalog.ClosedNodes)));
        var withMaterializer = System.Text.Json.Nodes.JsonNode.Parse(payload.GetRawText())!.AsObject();
        withMaterializer["input"] = new System.Text.Json.Nodes.JsonObject
        {
            ["descriptor_selector"] = PathFor("A"),
            ["materializer"] = "repository-snapshot-v1",
        };

        var exception = Assert.Throws<FormatException>(() =>
            FrozenLedger.ParseAcceptedEventDescriptorPath(
                "Freeze",
                JsonSerializer.SerializeToElement(withMaterializer)));

        Assert.Contains("unknown, missing, or duplicate fields", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CurrentFreezeWriterOmitsTheConstantOnlyVerdictFamily()
    {
        var catalog = BuildCatalog(Module("A"));
        var payload = FrozenLedgerCanonicalWriter.FreezeElement(
            FrozenLedgerCanonicalWriter.FreezePayload(
                Assert.Single(catalog.ClosedNodes)));

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

    private static int SchemaVersion(ImmutableArray<byte> bytes)
    {
        using var document = JsonDocument.Parse(bytes.AsSpan()[..^1].ToArray());
        return document.RootElement.GetProperty("schema_version").GetInt32();
    }

    private static JsonElement WithSchemaVersion(ImmutableArray<byte> bytes, int schemaVersion)
    {
        using var document = JsonDocument.Parse(bytes.AsSpan()[..^1].ToArray());
        var root = System.Text.Json.Nodes.JsonNode.Parse(document.RootElement.GetRawText())!.AsObject();
        root["schema_version"] = schemaVersion;
        return JsonSerializer.SerializeToElement(root);
    }

    private static void AssertRejectedByCandidateReader(
        JsonElement value,
        string eventType,
        int expectedVersion)
    {
        Assert.False(FrozenLedgerCanonicalWriter.ValidateDagEvent(
            value,
            out _,
            out _,
            out var validationMessage));
        var expected = $"content-addressed {eventType} schema_version must be {expectedVersion}.";
        Assert.Equal(expected, validationMessage);
    }

}
