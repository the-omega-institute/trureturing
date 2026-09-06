using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    [Fact]
    public void Ingest_ConcurrentExistingLedgerEditDoesNotBlockAppend()
    {
        var document = Ledger();
        var fixture = Fixture(document);
        fixture.Files[AlphaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var path = AtomPath(document.RequireDigestionSources()[0].Entries[0]);
        var fullPath = Path.Combine(temporary.Path, path);
        File.AppendAllText(fullPath, "# concurrent edit to an existing entry\n");
        var before = File.ReadAllBytes(fullPath);

        var result = Environment(fixture, temporary).Ingest(Arguments("alpha"));

        Assert.True(result.Success, result.Error);
        Assert.Equal(before, File.ReadAllBytes(fullPath));
        AssertSummary(result, residualOpenAdded: 1, skippedExisting: 1);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_ExistingUnemittableScalarDoesNotBlockNewAtom(bool sourceScoped)
    {
        var document = Ledger();
        var fixture = Fixture(document);
        var entry = document.RequireDigestionSources()[0].Entries[0];
        var path = AtomPath(entry);
        fixture.Files[path] = fixture.Files[path].Replace(
            "unresolved_subitems: []",
            "unresolved_subitems:\n    - 'legacy # retained'",
            StringComparison.Ordinal);
        var loaded = BackfillInventoryLoader.Load(Decode(Raw(fixture.Files)))
            .RequireDigestionEntries().Single(item => item.AtomId == entry.AtomId);
        Assert.Equal("legacy # retained", Assert.Single(loaded.Receipts.UnresolvedSubitems));
        Assert.Throws<FormatException>(() => BackfillInventoryWriter.WriteAtom(loaded));
        fixture.Files[AlphaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = Raw(fixture.Files);

        var result = Environment(fixture, temporary).Ingest(
            sourceScoped ? Arguments("alpha") : Arguments());

        Assert.True(result.Success, result.Error);
        var after = Overlay(temporary, fixture);
        foreach (var oldFile in before.Entries)
            Assert.Equal(oldFile.Bytes.ToArray(), after.Entries.Single(item => item.Path == oldFile.Path).Bytes.ToArray());
        var added = BackfillInventoryLoader.Load(Decode(after)).RequireDigestionEntries()
            .ExceptBy(document.RequireDigestionEntries().Select(static item => item.AtomId),
                static item => item.AtomId).ToArray();
        Assert.Equal("alpha", Assert.Single(added).SourceId);
        AssertSummary(result, residualOpenAdded: 1, skippedExisting: sourceScoped ? 1 : 2);
    }

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
        const string first = "  - gid: D5/S0/Carrier/Alpha.a\n    target_statement_id: null\n";
        const string second = "  - gid: D5/S0/Carrier/Zeta.z\n    target_statement_id: null\n";
        Assert.Contains(first + second, fixture.Files[path], StringComparison.Ordinal);
        fixture.Files[path] = fixture.Files[path].Replace(first + second, second + first, StringComparison.Ordinal);
        Assert.True(fixture.Files[path].IndexOf(second, StringComparison.Ordinal)
            < fixture.Files[path].IndexOf(first, StringComparison.Ordinal));
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
