using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
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
        var history = GenerateHistory(recordedCatalog);

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(LoadedHistory(history.AsSpan()), currentCatalog));

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
        var history = GenerateHistory(recordedCatalog);

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistory(LoadedHistory(history.AsSpan()), currentCatalog));

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
        var history = GenerateHistory(recordedCatalog);

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistory(LoadedHistory(history.AsSpan()), currentCatalog));

        Assert.Contains("statement identity changed", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void HistoricalComparisonAllowsDifferentRecordedAxiomClosureWhenCurrentClosureIsStandard()
    {
        var recordedCatalog = BuildCatalog(Module("A"));
        var currentCatalog = BuildCatalog(Module("A", axioms: ["propext"]));
        var history = GenerateHistory(recordedCatalog);

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(LoadedHistory(history.AsSpan()), currentCatalog));

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
        var history = GenerateHistory(recordedCatalog);

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistory(LoadedHistory(history.AsSpan()), currentCatalog));

        Assert.Contains("standard axiom allowlist", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void HistoricalComparisonAllowsRecordedContentAddressesToDiffer()
    {
        var catalog = BuildCatalog(Module("A"));
        var history = RewriteFreezePayload(GenerateHistory(catalog), payload =>
        {
            var recordedFrozen = FrozenNodeId.Create(Sha256("recorded frozen identity"));
            payload["case_id"] = FrozenLedgerCanonicalWriter.CaseId(recordedFrozen);
            payload["frozen_node_id"] = recordedFrozen.Value;
            payload["prerequisite_frozen_node_ids"] = new JsonArray(
                Sha256("unresolvable recorded prerequisite identity"));
            payload["witness_id"] = Sha256("recorded witness identity");
        });

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(LoadedHistory(history), catalog));

        Assert.Single(accepted.Capability.ActiveFrozenNodes);
    }

    [Fact]
    public void HistoricalComparisonRejectsPrerequisitePathDrift()
    {
        var recordedCatalog = BuildCatalog(Module("A"), Module("B"));
        var currentCatalog = BuildCatalog(
            Module("A"),
            Module("B", imports: new[] { "A" }));
        var history = GenerateHistory(recordedCatalog);

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateHistory(LoadedHistory(history.AsSpan()), currentCatalog));

        Assert.Contains(PathFor("B"), rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void NewFreezeWithNoncanonicalWitnessOrFrozenNodeIdIsRejected()
    {
        var catalog = BuildCatalog(Module("A"));
        var canonical = GenerateHistory(catalog);
        var badWitness = RewriteFreezePayload(canonical, payload =>
            payload["witness_id"] = Sha256("noncanonical witness identity"));
        var badFrozenNode = RewriteFreezePayload(canonical, payload =>
            payload["frozen_node_id"] = Sha256("noncanonical frozen identity"));

        Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(LoadedHistory(badWitness), catalog));
        Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(LoadedHistory(badFrozenNode), catalog));
    }

    [Fact]
    public void ReorderingAnyBaselineLineFailsTheExactCandidatePrefix()
    {
        var catalog = BuildCatalog(Module("A"), Module("B"));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes.AsSpan())).Syntax,
                catalog)).Capability;
        var lines = Lines(bytes);
        (lines[1], lines[2]) = (lines[2], lines[1]);
        var reordered = lines.SelectMany(static line => line).ToArray();

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(reordered)).Syntax,
                baseline,
                catalog));

        Assert.Contains("prefix", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void FreezeOfAnOpenNodeFailsEvenWithAValidCaseAndEventHash()
    {
        const string pathText = "D5/X_Frontier/OpenCase.lean";
        const string source = "-- D5-T0042\ntheorem openCase : True := by sorry\n";
        var catalog = Assert.IsType<FrozenMaterialOutcome.Accepted>(BuildCatalogOutcome(
            pathText,
            source,
            new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray.Create(new LeanDeclaration(
                    "openCase",
                    "theorem",
                    "True",
                    ImmutableArray.Create("sorryAx")))))).Capability;
        var genesisBytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var genesis = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(genesisBytes.AsSpan())).Syntax,
                catalog)).Capability;
        Assert.True(RepoPath.TryCreate(pathText, out var path));
        var statement = StatementId.Create(Sha256("statement"));
        var witness = WitnessId.Create(Sha256("witness"));
        var frozen = FrozenNodeId.Create(Sha256("frozen"));
        var payload = new FrozenFreezePayload(
            "active-frozen",
            ImmutableArray<FrozenDeclarationStatement>.Empty,
            frozen,
            new FrozenLedgerInput(
                catalog.Environment.OriginCommitOid,
                catalog.Environment.OriginTreeOid,
                GitBlobOid(source),
                pathText,
                new[]
                {
                    catalog.Environment.LakeManifestBlobOid,
                    catalog.Environment.LeanToolchainBlobOid,
                }.Order(StringComparer.Ordinal).ToImmutableArray()),
            ImmutableArray<FrozenNodeId>.Empty,
            statement,
            witness)
        {
            AxiomClosure = ImmutableArray<string>.Empty,
        };
        var line = FrozenLedgerCanonicalWriter.WriteEvent(
            "Freeze",
            FrozenLedgerCanonicalWriter.FreezeElement(payload),
            genesis.HeadHash,
            1).Bytes;
        var forged = genesisBytes.Concat(line).ToArray();

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(forged)).Syntax,
                catalog));

        Assert.Contains("non-Closed", rejected.Message, StringComparison.Ordinal);
    }

    private static ImmutableArray<byte> GenerateHistory(FrozenMaterialCatalog catalog) =>
        FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));

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

    private static FrozenLedgerSyntax LoadedHistory(ReadOnlySpan<byte> bytes) =>
        Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

    private static byte[] RewriteFreezePayload(
        ImmutableArray<byte> history,
        Action<JsonObject> rewrite)
    {
        var lines = Lines(history);
        Assert.Equal(2, lines.Length);
        using var document = JsonDocument.Parse(lines[1].AsMemory(0, lines[1].Length - 1));
        var root = document.RootElement;
        var payload = JsonNode.Parse(root.GetProperty("payload").GetRawText())!.AsObject();
        rewrite(payload);
        var rewritten = FrozenLedgerCanonicalWriter.WriteEvent(
            "Freeze",
            JsonSerializer.SerializeToElement(payload),
            root.GetProperty("previous_hash").GetString()!,
            1).Bytes;
        return lines[0].Concat(rewritten).ToArray();
    }

}
