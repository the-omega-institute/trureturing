using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_ExistingAtomIdAnywhereIsSkippedUntouched(bool sourceScoped)
    {
        var atom = Atom(AlphaText);
        var stored = Atom(BetaText);
        var existing = DigestionTestSupport.Entry(
            stored,
            atom.Fingerprints.RawSha256["sha256:".Length..],
            AtomizerRegistry.GenericId,
            sourceId: "beta",
            sourcePath: BetaPath) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
        };
        var current = TwoSourceLedger(
            EmptySource("alpha", AlphaPath),
            Source("beta", BetaPath, BetaText) with
            {
                Entries = [existing],
            });
        var baseline = TwoSourceLedger(
            EmptySource("alpha", AlphaPath),
            EmptySource("beta", BetaPath));
        var fixture = RobustFixture(current, baseline, AlphaText, AlphaText);
        var existingPath = $"{SourcePrefix("beta")}absorbed-closed/{existing.AtomId}.yaml";
        fixture.Files[existingPath] = "# byte witness\r\n"
            + fixture.Files[existingPath].Replace("\n", "\r\n", StringComparison.Ordinal);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = Environment(fixture, temporary).Ingest(
            sourceScoped ? Arguments("alpha") : Arguments());

        Assert.True(result.Success, result.Error);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        AssertSummary(
            result,
            residualOpenAdded: 0,
            skippedExisting: sourceScoped ? 1 : 2);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_ExistingNonCanonicalEntryIsSkippedWithoutError(bool sourceScoped)
    {
        var document = Ledger();
        var alpha = document.RequireDigestionSources()[0];
        var entry = alpha.Entries[0] with
        {
            Coverage =
            [
                new DigestionCoverageEdge("D5/S0/Carrier/Zeta.z", null),
                new DigestionCoverageEdge("D5/S0/Carrier/Alpha.a", null),
            ],
        };
        document = document.WithDigestionSources(
        [
            alpha with { Entries = [entry] },
            document.RequireDigestionSources()[1],
        ]);
        var fixture = Fixture(document);
        var path = AtomPath(entry);
        fixture.Files[path] = "# preserve non-canonical bytes\r\n"
            + fixture.Files[path].Replace("\n", "\r\n", StringComparison.Ordinal);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = Environment(fixture, temporary).Ingest(
            sourceScoped ? Arguments("alpha") : Arguments());

        Assert.True(result.Success, result.Error);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        AssertSummary(result, residualOpenAdded: 0, skippedExisting: sourceScoped ? 1 : 2);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_ExistingUnchainedParentIsSkippedWithoutChildren(bool sourceScoped)
    {
        var alpha = Source("alpha", AlphaPath, ClauseText);
        var ledger = TwoSourceLedger(alpha, Source("beta", BetaPath, BetaText));
        var fixture = Fixture(ledger, ClauseText, BetaText);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = Environment(fixture, temporary).Ingest(
            sourceScoped ? Arguments("alpha") : Arguments());

        Assert.True(result.Success, result.Error);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        var source = BackfillInventoryLoader.LoadRoot(temporary.Path)
            .RequireDigestionSources()
            .Single(static candidate => candidate.SourceId == "alpha");
        Assert.Empty(Assert.Single(source.Entries).Receipts.ChainAtoms);
        AssertSummary(result, residualOpenAdded: 0, skippedExisting: sourceScoped ? 1 : 2);
    }

    [Fact]
    public void Ingest_RemovedBaselineAtomIsNotResurrected()
    {
        var baseline = TwoSourceLedger(
            Source("alpha", AlphaPath, ClauseText),
            Source("beta", BetaPath, BetaText));
        var current = TwoSourceLedger(
            EmptySource("alpha", AlphaPath),
            baseline.RequireDigestionSources()[1]);
        var removed = Assert.Single(baseline.RequireDigestionSources()[0].Entries);
        var fixture = RobustFixture(current, baseline, ClauseText, BetaText);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = Environment(fixture, temporary).Ingest(Arguments("alpha"));

        Assert.True(result.Success, result.Error);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        Assert.DoesNotContain(
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries(),
            entry => entry.AtomId == removed.AtomId);
        AssertSummary(result, residualOpenAdded: 0, skippedExisting: 0);
    }

    private static void AssertSummary(
        StrataLint.Cli.CommandResult result,
        int residualOpenAdded,
        int skippedExisting)
    {
        var summary = Assert.Single(result.Output.Split('\n'), static line =>
            line.StartsWith("INGEST ", StringComparison.Ordinal));
        Assert.StartsWith(
            $"INGEST residual_open_added={residualOpenAdded} skipped_existing={skippedExisting} ",
            summary,
            StringComparison.Ordinal);
        Assert.DoesNotContain("stale_acknowledged=", summary, StringComparison.Ordinal);
    }
}
