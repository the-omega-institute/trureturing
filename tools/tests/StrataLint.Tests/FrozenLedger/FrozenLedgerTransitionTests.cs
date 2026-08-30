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
    public void LedgerAppendReanchorsStalePrerequisiteClosureWithoutRewritingAcceptedFreeze()
    {
        var catalog = BuildCatalog(
            Module("C"),
            Module("A", imports: ["C"]),
            Module("B", imports: ["A"]));
        var currentC = catalog.ByPath[RepoPathFor("C")];
        var currentA = catalog.ByPath[RepoPathFor("A")];
        var currentB = catalog.ByPath[RepoPathFor("B")];
        var obsoleteC = FrozenNodeId.Create(Sha256("obsolete C coordinate"));
        var staleA = currentA with
        {
            FrozenNodeId = FrozenContentAddress.ComputeFrozenNodeId(
                currentA.RepoPath,
                currentA.StatementId,
                [obsoleteC]),
            PrerequisiteFrozenNodeIds = [obsoleteC],
        };
        var staleB = currentB with
        {
            FrozenNodeId = FrozenContentAddress.ComputeFrozenNodeId(
                currentB.RepoPath,
                currentB.StatementId,
                [staleA.FrozenNodeId]),
            PrerequisiteFrozenNodeIds = [staleA.FrozenNodeId],
        };
        var acceptedFiles = ImmutableArray.Create(
            EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(currentC))),
            EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(staleA))),
            EventFile("Freeze", FrozenLedgerCanonicalWriter.FreezeElement(
                FrozenLedgerCanonicalWriter.FreezePayload(staleB))));
        var originalBytes = acceptedFiles.ToDictionary(
            static file => file.Path,
            static file => file.RawBytes);
        var baseView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            acceptedFiles.ToImmutableDictionary(static file => file.Path)));
        var baseline = baseView.ToWriterBaseline();

        var drafts = FrozenLedgerGenerator.MissingFreezes(baseline, catalog);

        Assert.Equal(["A", "B"], drafts.Select(draft =>
            Path.GetFileNameWithoutExtension(
                draft.Payload.GetProperty("descriptor_selector").GetString())));
        Assert.All(drafts, static draft => Assert.Equal("Reanchor", draft.EventType));
        Assert.All(acceptedFiles, file => Assert.Equal(originalBytes[file.Path], file.RawBytes));
        var suffix = LoadDrafts(baseView, drafts);
        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(suffix, baseline, catalog));
        Assert.Equal(
            catalog.ClosedNodes.Select(static node => node.FrozenNodeId),
            accepted.Capability.ActiveFrozenNodes.Select(static node => node.FrozenNodeId));
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
