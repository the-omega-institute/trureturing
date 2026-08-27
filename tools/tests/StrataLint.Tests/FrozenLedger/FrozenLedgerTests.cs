using System.Reflection;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void LedgerCapabilityAndContentAddressIdentifiersHaveNoPublicConstructors()
    {
        Assert.Empty(typeof(FrozenLedgerConsistent).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(FrozenMaterialCatalog).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(StatementId).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(WitnessId).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(FrozenNodeId).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(TrustedFrozenGitReferences).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
    }

    [Fact]
    public void CorpusRootCaseLeafPreimageIsPinnedToCurrentFreezePayload()
    {
        var catalog = BuildCatalog(Module("A"));
        var payload = FrozenLedgerCanonicalWriter.FreezePayload(
            catalog.Environment,
            Assert.Single(catalog.ClosedNodes));
        var currentFreezePreimage = StructuredCanonicalWriter.WriteJson(
            FrozenLedgerCanonicalWriter.FreezeElement(payload));
        var expected = FrozenContentHash.Compute(
            FrozenHashDomains.FrozenCase,
            currentFreezePreimage.AsSpan());

        Assert.Equal(
            "sha256:2219348d155a6812eeb24a44d078ed9aadb1ef5e2596bbd38ff28b89823ad231",
            expected);
        Assert.Equal(expected, FrozenLedger.ComputeCaseLeaf(payload));
        Assert.Matches("^sha256:[0-9a-f]{64}$", Baseline(catalog).CorpusRoot);
    }

    [Fact]
    public void ReferenceProjectionRejectsUnknownFieldsInDagPayload()
    {
        var events = LoadEvents(EventFiles(BuildCatalog(Module("A"))));
        var freeze = Assert.Single(events, static item => item.EventType == "Freeze");
        var payload = JsonNode.Parse(freeze.Payload.GetRawText())!.AsObject();
        payload["unknown"] = true;
        var forged = events.Replace(
            freeze,
            freeze with { Payload = JsonSerializer.SerializeToElement(payload) });

        var rejected = Assert.IsType<FrozenLedgerReferenceScanOutcome.Rejected>(
            FrozenLedger.ScanReferences(forged));

        Assert.Contains("unknown", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void DagWriterEnvelopeHasNoLinearReplayCoordinates()
    {
        var files = EventFiles(BuildCatalog(Module("A")));
        var freeze = Assert.Single(LoadEvents(files), static item => item.EventType == "Freeze");
        var file = files.Single(item => item.Path == freeze.SourcePath);
        using var document = JsonDocument.Parse(file.RawBytes.AsSpan()[..^1].ToArray());
        var fields = document.RootElement.EnumerateObject()
            .Select(static property => property.Name)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(["event_hash", "event_type", "payload", "schema_version"], fields);
    }
}
