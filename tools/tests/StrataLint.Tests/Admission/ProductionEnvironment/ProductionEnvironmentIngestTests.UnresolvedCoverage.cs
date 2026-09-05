using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void AlignDigestionStatusProjectsMixedResolvedAndNullCoverageToPartialOpen()
    {
        AssertUnresolvedCoverageProjectsToPartialOpen(includeResolvedEdge: true);
    }

    [Fact]
    public void AlignDigestionStatusProjectsOnlyNullCoverageToPartialOpen()
    {
        AssertUnresolvedCoverageProjectsToPartialOpen(includeResolvedEdge: false);
    }

    private static void AssertUnresolvedCoverageProjectsToPartialOpen(bool includeResolvedEdge)
    {
        const string resolvedGid = "D5/S0/Carrier/Ring";
        const string unresolvedGid = "D5/E/values--json";
        const string sourceId = "unresolved-coverage";
        var fixture = new RuleFixture();
        Assert.True(Gid.TryParse(unresolvedGid, out var unresolved));
        fixture.Files[unresolved.Path.Value] = "{}\n";
        fixture.Baseline[unresolved.Path.Value] = "{}\n";
        var targetStatementId = FrozenStatementReceiptTestData.Id('d');
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            FrozenStatementReceiptTestData.AddLedger(
                files,
                new FrozenStatementReceiptTestData.Module(
                    RuleFixture.RingPath,
                    targetStatementId,
                    []));
        }

        var atom = DigestionAtom.FromFrozenCas(
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("unresolved coverage fixture\n")));
        var atomId = AtomId(atom);
        var coverage = includeResolvedEdge
            ? ImmutableArray.Create(
                new DigestionCoverageEdge(resolvedGid, targetStatementId),
                new DigestionCoverageEdge(unresolvedGid, null))
            : ImmutableArray.Create(new DigestionCoverageEdge(unresolvedGid, null));
        var entry = DigestionTestSupport.Entry(
            atom,
            atomId,
            AtomizerRegistry.NoAtomizerId,
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed,
            coverage.Select(static edge => edge.Gid).ToImmutableArray(),
            sourceId: sourceId,
            sourcePath: RuleFixture.FixtureDigestionSourcePath) with
        {
            Coverage = coverage,
        };
        var document = DigestionTestSupport.Document(
            AtomizerRegistry.NoAtomizerId,
            [entry],
            sourceId,
            RuleFixture.FixtureDigestionSourcePath);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, document);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, document);
        var casPath = DigestionCasStore.RootPath + atomId;
        var casText = Encoding.UTF8.GetString(atom.RawBytes.AsSpan());
        fixture.Files[casPath] = casText;
        fixture.Baseline[casPath] = casText;
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.Contains("target-statement-unresolved", result.Output, StringComparison.Ordinal);
        var projected = Assert.Single(
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries());
        Assert.Equal(DigestionMigrationState.Partial, projected.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, projected.ProjectedStatus.Truth);
        Assert.True(File.Exists(Path.Combine(
            temporary.Path,
            DirectoryAtomPath(sourceId, atomId, "partial-open")
                .Replace('/', Path.DirectorySeparatorChar))));
        Assert.False(File.Exists(Path.Combine(
            temporary.Path,
            DirectoryAtomPath(sourceId, atomId, "partial-closed")
                .Replace('/', Path.DirectorySeparatorChar))));
    }
}
