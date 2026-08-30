using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void AdmissionCatalogUsesActiveV5LedgerIdentityForSelectedImportedDeclaration()
    {
        var modules = new[]
        {
            Module("A"),
            Module("B", imports: ["A"]),
        };
        var baseCatalog = BuildCatalog(modules);
        var activePrerequisite = FrozenNodeId.Create(Sha256("active v5 prerequisite"));
        var activeLedgerOwner = baseCatalog.ByPath[RepoPathFor("A")] with
        {
            PrerequisiteFrozenNodeIds = [activePrerequisite],
            FrozenNodeId = FrozenContentAddress.ComputeFrozenNodeId(
                RepoPathFor("A"),
                baseCatalog.ByPath[RepoPathFor("A")].StatementId,
                [activePrerequisite]),
        };
        var acceptedLedgerEvent = EventFile(
            "Freeze",
            FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(activeLedgerOwner)));
        var acceptedView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            ImmutableDictionary<RepoPath, RepositoryFile>.Empty.Add(
                acceptedLedgerEvent.Path,
                acceptedLedgerEvent)));

        var candidate = BuildAdmissionCatalog(
            ["A", "B"],
            acceptedView.ActiveByPath.ToDictionary(
                static item => item.Key,
                static item => item.Value.Material),
            modules);

        Assert.Equal(
            acceptedView.ActiveByPath[RepoPathFor("A")].Material.FrozenNodeId,
            Assert.Single(candidate.ByPath[RepoPathFor("B")].PrerequisiteFrozenNodeIds));
    }

    [Fact]
    public void ProofBodyOnlyChangeDoesNotReportStatementIdentityChanged()
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
    public void StatementChangeReportsActiveModuleStatementIdentityChanged()
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
        Assert.Contains("statement identity changed", rejected.Message, StringComparison.Ordinal);
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

    private static FrozenMaterialCatalog ReplaceMaterial(
        FrozenMaterialCatalog catalog,
        FrozenNodeMaterial material) =>
        FrozenMaterialCatalog.Create(
            catalog.States,
            [material],
            catalog.OpenCases,
            catalog.TailRegistrations,
            catalog.Adjacency);

}
