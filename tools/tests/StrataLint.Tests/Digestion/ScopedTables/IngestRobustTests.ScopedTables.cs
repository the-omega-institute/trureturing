using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    [Fact]
    public void Ingest_ScopedTableRepairAddsCompleteAtomAndRetainsStoredAtomsAndStates()
    {
        const string prefix = "**命题 5.1**。设参数非零。\n\n| 条件 | 值 |\n| --- | --- |\n";
        const string row = "| 正 | 1 |";
        const string complete = prefix + row + "\n\n因此极限等于 3。\n\n*证明*。代入并约分。\n\n";
        var oldPrefix = DigestionAtom.FromFrozenCas([.. Encoding.UTF8.GetBytes(prefix)]);
        var oldRow = DigestionAtom.FromFrozenCas([.. Encoding.UTF8.GetBytes(row[..^1])]);
        var oldEntries = new[] { oldPrefix, oldRow }.Select(atom => DigestionTestSupport.Entry(
            atom, atom.Fingerprints.RawSha256[7..], AtomizerRegistry.GenericId,
            migration: DigestionMigrationState.Absorbed, truth: DigestionTruthState.Closed,
            coverageGids: ["D5/S0/Synthetic/Receipt.probe"], sourceId: "alpha", sourcePath: AlphaPath))
            .ToImmutableArray();
        var alpha = EmptySource("alpha", AlphaPath) with { Entries = oldEntries };
        var ledger = TwoSourceLedger(alpha, Source("beta", BetaPath, BetaText));
        var fixture = RobustFixture(ledger, ledger, complete, BetaText);
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            AddCas(files, oldPrefix);
            AddCas(files, oldRow);
        }
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);

        var result = Environment(fixture, temporary).Ingest(Arguments("alpha"));

        Assert.True(result.Success, result.Error);
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        AssertExistingLedgerFilesUnchanged(before, after);
        var entries = BackfillInventoryLoader.Load(Decode(after)).RequireDigestionEntries();
        foreach (var old in oldEntries)
        {
            var retained = Assert.Single(entries, entry => entry.AtomId == old.AtomId);
            Assert.Equal(old.ProjectedStatus, retained.ProjectedStatus);
            Assert.Equal(old.CasRef, retained.CasRef);
            Assert.Equal(old.Coverage.ToArray(), retained.Coverage.ToArray());
        }
        var expected = DigestionCasStore.Capture(Encoding.UTF8.GetBytes(complete));
        var added = Assert.Single(entries, entry => entry.AtomId == expected.Reference[7..]);
        Assert.Equal(DigestionMigrationState.Residual, added.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, added.ProjectedStatus.Truth);
        Assert.Equal(expected.Bytes.ToArray(), after.Entries.Single(file => file.Path == expected.RelativePath).Bytes.ToArray());
        AssertSummary(result, residualOpenAdded: 1, skippedExisting: 0);

        fixture.Files.Clear();
        foreach (var file in after.Entries)
            fixture.Files.Add(file.Path, Encoding.UTF8.GetString(file.Bytes.AsSpan()));
        var afterImage = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var repeated = Environment(fixture, temporary).Ingest(Arguments("alpha"));
        Assert.True(repeated.Success, repeated.Error);
        Assert.Equal(afterImage, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        AssertSummary(repeated, residualOpenAdded: 0, skippedExisting: 1);
    }
}
