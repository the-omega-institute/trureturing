using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void IngestAlignsInputCoverageBeforeProjectingStatuses()
    {
        AssertCoverageAlignmentPrecedesStatusProjection();
        using var temporary = new TemporaryDirectory();
        var environment = ReceiptIntegrityStatusProjectionEnvironment(
            temporary.Path,
            includeInputMismatch: true);

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        var edge = Assert.Single(BackfillInventoryLoader.LoadRoot(temporary.Path)
            .RequireDigestionEntries()
            .SelectMany(static entry => entry.Coverage));
        Assert.Null(edge.TargetStatementId);
    }

    [Fact]
    public void IngestPostProjectionReceiptIntegrityGatePrecedesBackfillValidation()
    {
        AssertIngestReceiptIntegrityGate(
            "evaluation",
            "var evaluation = DigestionStatusEvaluator.Evaluate(",
            "var backfillObservations = DigestionBackfillValidation.RequireValidBackfill(");
    }

    private static void AssertIngestReceiptIntegrityGate(
        string evaluation,
        string precedingAnchor,
        string followingAnchor)
    {
        var source = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools",
            "StrataLint.Cli",
            "Commands",
            "Digestion",
            "IngestCommand.cs"));
        var preceding = source.IndexOf(precedingAnchor, StringComparison.Ordinal);
        var gate = source.IndexOf(
            $"RequireNoReceiptIntegrityFailure({evaluation});",
            StringComparison.Ordinal);
        var following = source.IndexOf(followingAnchor, StringComparison.Ordinal);

        Assert.True(preceding >= 0, $"Missing ingest control-flow anchor: {precedingAnchor}");
        Assert.True(gate > preceding, $"Missing receipt-integrity gate for {evaluation}");
        Assert.True(following > gate, $"Receipt-integrity gate for {evaluation} moved past its write boundary");
    }

    private static void AssertCoverageAlignmentPrecedesStatusProjection()
    {
        var source = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools",
            "StrataLint.Cli",
            "Commands",
            "Digestion",
            "IngestCommand.cs"));
        var align = source.IndexOf(
            "plannedDocument = DigestionCoverageTargetAligner.Align(",
            StringComparison.Ordinal);
        var projection = source.IndexOf(
            "var derived = DigestionStatusEvaluator.Evaluate(",
            StringComparison.Ordinal);

        Assert.True(align >= 0, "Missing current coverage target alignment");
        Assert.True(projection > align, "Coverage target alignment moved after status projection");
    }

    private static ProductionCliEnvironment ReceiptIntegrityStatusProjectionEnvironment(
        string repositoryRoot,
        bool includeInputMismatch)
    {
        const string coverageGid = "D5/S0/Carrier/Ring";
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。old。\n\n**定理 1.2(B)**。stable。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。stable。\n");
        var oldAtoms = AtomizerRegistry.Atomize(
            atomizerId,
            oldBytes,
            DigestionTestSupport.Rules).Claims;
        Assert.Equal(2, oldAtoms.Length);
        var oldGeneration = oldAtoms[0];
        var stableGeneration = oldAtoms[1];
        var oldGenerationId = AtomId(oldGeneration);
        var stableGenerationId = AtomId(stableGeneration);
        var stableEntry = DigestionTestSupport.Entry(
            stableGeneration,
            stableGenerationId,
            atomizerId,
            coverageGids: [],
            sourceId: "fixture-source",
            sourcePath: RuleFixture.FixtureDigestionSourcePath) with
        {
            Coverage = includeInputMismatch
                ? [new DigestionCoverageEdge(
                    coverageGid,
                    "sha256:" + new string('c', 64))]
                : [],
        };
        var document = DigestionTestSupport.Document(
            atomizerId,
            [
                DigestionTestSupport.Entry(
                    oldGeneration,
                    oldGenerationId,
                    atomizerId,
                    migration: DigestionMigrationState.Partial,
                    sourceId: "fixture-source",
                    sourcePath: RuleFixture.FixtureDigestionSourcePath),
                stableEntry,
            ],
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            GenreRegistryCheck.Collected([]));
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallProjectedLedger(fixture, document, existingAtom: null);
        var source = Assert.Single(document.RequireDigestionSources());
        var baselineDocument = document.WithDigestionSources(
        [
            source with
            {
                Entries = source.Entries.Select(entry => entry.AtomId == oldGenerationId
                    ? entry with
                    {
                        ProjectedStatus = new DigestionStatus(
                            DigestionMigrationState.Residual,
                            DigestionTruthState.Open),
                    }
                    : entry).ToImmutableArray(),
            },
        ]);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, baselineDocument);
        foreach (var atom in oldAtoms)
        {
            var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
            var text = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
            fixture.Files[captured.RelativePath] = text;
            fixture.Baseline[captured.RelativePath] = text;
        }

        WriteDirectoryLedger(repositoryRoot, fixture.Files);
        return new ProductionCliEnvironment(
            repositoryRoot,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));
    }
}
