using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class FrozenContentAddressTests
{
    [Fact]
    public void ProofOnlyRewritePreservesStatementIdAndChangesWitnessAndFrozenNodeIds()
    {
        var first = BuildCatalog(Module("A", source: "theorem a : True := by trivial\n"));
        var second = BuildCatalog(Module("A", source: "theorem a : True := by exact True.intro\n"));

        var firstNode = Assert.Single(first.ClosedNodes);
        var secondNode = Assert.Single(second.ClosedNodes);
        Assert.Equal(firstNode.StatementId, secondNode.StatementId);
        Assert.NotEqual(firstNode.WitnessId, secondNode.WitnessId);
        Assert.NotEqual(firstNode.FrozenNodeId, secondNode.FrozenNodeId);
    }

    [Fact]
    public void FreezeCarriesDeclarationStatementIdsWithoutCopyingStatementMaterial()
    {
        var catalog = BuildCatalog(Module("A"));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var line = Lines(bytes)[1];
        using var document = JsonDocument.Parse(line.AsMemory(0, line.Length - 1));

        var payload = document.RootElement.GetProperty("payload");
        Assert.True(payload.TryGetProperty("declaration_statement_ids", out var declarationStatementIds));
        var reference = Assert.Single(declarationStatementIds.EnumerateArray());
        Assert.False(reference.TryGetProperty("declaration_name", out _));
        Assert.Equal("ns(n0,1:a)", reference.GetProperty("declaration_name_key").GetString());
        Assert.Equal("theorem", reference.GetProperty("kind").GetString());
        Assert.Matches(
            "^sha256:[0-9a-f]{64}$",
            reference.GetProperty("statement_id").GetString());
        Assert.DoesNotContain("statement_material", payload.GetRawText(), StringComparison.Ordinal);
    }

    [Fact]
    public void ForgedDeclarationStatementIdFailsAfterCanonicalEventRehash()
    {
        var catalog = BuildCatalog(Module("A"));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var lines = Lines(bytes);
        using var genesisDocument = JsonDocument.Parse(
            lines[0].AsMemory(0, lines[0].Length - 1));
        using var freezeDocument = JsonDocument.Parse(
            lines[1].AsMemory(0, lines[1].Length - 1));
        var payload = JsonNode.Parse(
            freezeDocument.RootElement.GetProperty("payload").GetRawText())!.AsObject();
        payload["declaration_statement_ids"]!.AsArray()[0]!["statement_id"] =
            Sha256("forged-declaration");
        var forgedLine = FrozenLedgerCanonicalWriter.WriteEvent(
            "Freeze",
            JsonSerializer.SerializeToElement(payload),
            genesisDocument.RootElement.GetProperty("event_hash").GetString()!,
            1).Bytes;
        var forged = lines[0].Concat(forgedLine).ToArray();

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(forged)).Syntax,
                catalog));

        Assert.Contains("statement identity changed", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }
}
