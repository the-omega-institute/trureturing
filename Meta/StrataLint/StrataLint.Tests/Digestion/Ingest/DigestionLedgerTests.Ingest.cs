using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void IngestRebindsCasBackedNoAtomizerBoundaryAndRemainsByteIdempotent()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var atom = new DigestionAtom(
            "manual/receipt",
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            ImmutableArray<DigestionContext>.Empty);
        var ledgerText = LedgerYamlWithAtomizer(
            atom,
            migration: "partial",
            truth: "open",
            coverageReceipts: "[]",
            scribeReceipts: "[]",
            atomizer: AtomizerRegistry.NoAtomizerId);
        var ledger = BackfillInventoryLoader.Load(ledgerText);

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", sourceBytes), CasFile(atom)),
            ledger);
        var firstBytes = BackfillInventoryWriter.WriteForIngest(first.Document);
        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));

        var migratedEntry = Assert.Single(migrated.RequireDigestionEntries());
        Assert.NotNull(migratedEntry.Boundary);
        Assert.Equal(atom.Fingerprints.RawSha256, migratedEntry.CasRef);
        Assert.Empty(first.CasObjects);

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(
                ("docs/source.md", sourceBytes),
                CasFile(atom)),
            ledger);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }

    [Fact]
    public void IngestPassesThroughDirectoryNoAtomizerEntryWithoutBoundary()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var captured = DigestionCasStore.Capture(sourceBytes);
        var sourceId = "manual-specification";
        var atomId = "manual-receipt";
        var sourceMetadata = $$"""
            source_id = "{{sourceId}}"
            path = "docs/source.md"
            atomizer = "{{AtomizerRegistry.NoAtomizerId}}"
            """ + "\n";
        var atom = $$"""
            ast_path: manual/receipt
            fingerprints:
              raw_sha256: {{captured.Reference}}
              normalized_sha256: {{captured.Reference}}
            cas_ref: {{captured.Reference}}
            coverage_gids: []
            receipts:
              coverage: []
              scribe: []
              unresolved_subitems: []
            """ + "\n";
        var snapshot = Snapshot(
            ("docs/source.md", sourceBytes),
            (captured.RelativePath, captured.Bytes.ToArray()),
            ($"{BackfillInventoryLoader.RootPath}{sourceId}/source.toml",
                Encoding.UTF8.GetBytes(sourceMetadata)),
            ($"{BackfillInventoryLoader.RootPath}{sourceId}/partial-open/{atomId}.yaml",
                Encoding.UTF8.GetBytes(atom)),
            (BackfillInventoryLoader.TicketIndexPath, []));
        var ledger = BackfillInventoryLoader.Load(snapshot);
        var expected = Assert.Single(ledger.RequireDigestionEntries());

        var plan = DigestionIngestor.Plan(ledger, snapshot, ledger);

        Assert.Equal(expected, Assert.Single(plan.Document.RequireDigestionEntries()));
        Assert.Empty(plan.CasObjects);
    }

    [Fact]
    public void IngestOnboardsRegisteredEmptySourceAndRemainsByteIdempotent()
    {
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。first。\n\n**定理 1.2(B)**。second。\n");
        var atoms = AtomizerRegistry.Atomize(atomizerId, sourceBytes, DigestionTestSupport.Rules).Claims;
        var ledger = BackfillInventoryLoader.Load(EmptyLedger(atomizerId));

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", sourceBytes)),
            ledger);
        var firstBytes = BackfillInventoryWriter.WriteForIngest(first.Document);
        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));
        var entries = Assert.Single(first.Document.RequireDigestionSources()).Entries;

        Assert.Equal(atoms.Length, first.ResidualOpenAdded);
        Assert.Equal(atoms.Length, entries.Length);
        Assert.Equal(atoms.Length, first.CasObjects.Length);
        Assert.Empty(first.Fallbacks);
        Assert.All(entries, static entry =>
        {
            Assert.Null(entry.Boundary);
            Assert.Equal(entry.Fingerprints.RawSha256, entry.CasRef);
            Assert.Empty(entry.CoverageGids);
            Assert.Empty(entry.Receipts.Coverage);
            Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
        });
        Assert.All(first.CasObjects, item => Assert.Contains(
            atoms,
            atom => atom.Fingerprints.RawSha256 == item.Reference
                && atom.RawBytes.AsSpan().SequenceEqual(item.Bytes.AsSpan())));

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, first.CasObjects),
            ledger);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }

    [Fact]
    public void IngestOnboardsRegisteredEmptySourceWithCoarseFallback()
    {
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**未知 1.1(A)**。free-form source。\n");
        var ledger = BackfillInventoryLoader.Load(EmptyLedger(atomizerId));

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", sourceBytes)),
            ledger);
        var firstBytes = BackfillInventoryWriter.WriteForIngest(first.Document);
        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));

        var fallback = Assert.Single(first.Fallbacks);
        Assert.Equal("source", fallback.SourceId);
        Assert.Equal(1, first.ResidualOpenAdded);
        var coarse = Assert.Single(first.Document.RequireDigestionEntries());
        Assert.Equal("coarse/source", coarse.AstPath);
        Assert.Equal(DigestionMigrationState.Residual, coarse.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, coarse.ProjectedStatus.Truth);
        var captured = Assert.Single(first.CasObjects);
        Assert.Equal(coarse.Fingerprints.RawSha256, coarse.CasRef);
        Assert.Equal(sourceBytes, captured.Bytes.ToArray());

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, first.CasObjects),
            ledger);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }
}
