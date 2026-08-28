using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void HistoricalComparisonAllowsProofBodyChange()
    {
        var recordedCatalog = BuildCatalog(Module(
            "A",
            source: "theorem a : True := by trivial\n"));
        var currentCatalog = BuildCatalog(Module(
            "A",
            source: "theorem a : True := by exact True.intro\n"));

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(EventFiles(recordedCatalog), currentCatalog));

        Assert.Single(accepted.Capability.ActiveFrozenNodes);
    }

    [Fact]
    public void HistoricalComparisonRejectsRewrittenStatementAndNamesModulePath()
    {
        var recordedCatalog = BuildCatalog(Module("A"));
        var recordedMaterial = Assert.Single(recordedCatalog.ClosedNodes);
        var currentCatalog = ReplaceMaterial(
            recordedCatalog,
            recordedMaterial with
            {
                StatementId = StatementId.Create(Sha256("rewritten statement")),
            });

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistory(EventFiles(recordedCatalog), currentCatalog));

        Assert.Contains(PathFor("A"), rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void HistoricalComparisonRejectsAddedDeclaration()
    {
        var recordedCatalog = BuildCatalog(Module("A"));
        var recordedMaterial = Assert.Single(recordedCatalog.ClosedNodes);
        var currentCatalog = ReplaceMaterial(
            recordedCatalog,
            recordedMaterial with
            {
                DeclarationStatementIds = recordedMaterial.DeclarationStatementIds.Add(
                    new FrozenDeclarationStatement(
                        "ns(n0,5:extra)",
                        "theorem",
                        StatementId.Create(Sha256("added declaration")))),
            });

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistory(EventFiles(recordedCatalog), currentCatalog));

        Assert.Contains("statement identity changed", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void HistoricalComparisonAllowsDifferentRecordedAxiomClosureWhenCurrentClosureIsStandard()
    {
        var recordedCatalog = BuildCatalog(Module("A"));
        var currentCatalog = BuildCatalog(Module("A", axioms: ["propext"]));

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(EventFiles(recordedCatalog), currentCatalog));

        Assert.Single(accepted.Capability.ActiveFrozenNodes);
    }

    [Fact]
    public void HistoricalComparisonRejectsCurrentAxiomClosureOutsideStandardAllowlist()
    {
        var catalog = BuildCatalog(Module("A"));
        var material = Assert.Single(catalog.ClosedNodes) with
        {
            AxiomClosure = ["Nonstandard.axiom"],
        };
        var recordedCatalog = ReplaceMaterial(catalog, material);
        var currentCatalog = ReplaceMaterial(catalog, material);

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistory(EventFiles(recordedCatalog), currentCatalog));

        Assert.Contains("standard axiom allowlist", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void HistoricalComparisonAllowsRecordedContentAddressesToDiffer()
    {
        var catalog = BuildCatalog(Module("A"));
        var history = RewriteFreezePayload(EventFiles(catalog), payload =>
        {
            var recordedFrozen = FrozenNodeId.Create(Sha256("recorded frozen identity"));
            payload["case_id"] = FrozenLedgerCanonicalWriter.CaseId(recordedFrozen);
            payload["frozen_node_id"] = recordedFrozen.Value;
            payload["prerequisite_frozen_node_ids"] = new JsonArray(
                Sha256("unresolvable recorded prerequisite identity"));
            payload["witness_id"] = Sha256("recorded witness identity");
        });

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(history, catalog));

        Assert.Single(accepted.Capability.ActiveFrozenNodes);
    }

    [Fact]
    public void HistoricalComparisonRejectsPrerequisitePathDrift()
    {
        var recordedCatalog = BuildCatalog(Module("A"), Module("B"));
        var currentCatalog = BuildCatalog(
            Module("A"),
            Module("B", imports: new[] { "A" }));

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistory(EventFiles(recordedCatalog), currentCatalog));

        Assert.Contains(PathFor("B"), rejected.Message, StringComparison.Ordinal);
    }

    private static FrozenMaterialCatalog ReplaceMaterial(
        FrozenMaterialCatalog catalog,
        FrozenNodeMaterial material) =>
        FrozenMaterialCatalog.Create(
            catalog.Environment,
            catalog.States,
            [material],
            catalog.OpenCases,
            catalog.TailRegistrations,
            catalog.Adjacency);

    private static ImmutableArray<RepositoryFile> RewriteFreezePayload(
        ImmutableArray<RepositoryFile> history,
        Action<JsonObject> rewrite)
    {
        var freeze = Assert.Single(LoadEvents(history), static item => item.EventType == "Freeze");
        var freezeFile = history.Single(item => item.Path == freeze.SourcePath);
        using var document = JsonDocument.Parse(freezeFile.RawBytes.AsSpan()[..^1].ToArray());
        var payload = JsonNode.Parse(
            document.RootElement.GetProperty("payload").GetRawText())!.AsObject();
        rewrite(payload);
        return history.Replace(
            freezeFile,
            EventFile("Freeze", JsonSerializer.SerializeToElement(payload)));
    }
}
