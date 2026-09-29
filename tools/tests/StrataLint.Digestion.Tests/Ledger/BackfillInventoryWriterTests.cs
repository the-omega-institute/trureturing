using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Digestion.Tests;

public sealed class BackfillInventoryWriterTests
{
    private const string SourceId = "writer-v0.1";
    private const string SourcePath = "docs/develop/theory/writer.md";
    private const string AtomId = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string RawHash = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string NormalizedHash = "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    private const string AlphaGid = "D5/S0/Carrier/Alpha.alpha";
    private const string ZetaGid = "D5/S0/Carrier/Zeta.zeta";
    private const string AlphaTargetHash = "sha256:1111111111111111111111111111111111111111111111111111111111111111";
    private const string ZetaTargetHash = "sha256:2222222222222222222222222222222222222222222222222222222222222222";

    [Fact]
    public void BackfillInventoryWriter_WritesCoverageGidsInOrdinalOrder()
    {
        var entry = Entry(
            [
                new DigestionCoverageEdge(ZetaGid, ZetaTargetHash),
                new DigestionCoverageEdge(AlphaGid, AlphaTargetHash),
            ]);

        var written = Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan());

        Assert.Equal(CanonicalAtomText(), written);
    }

    [Fact]
    public void BackfillInventoryWriter_CanonicalInputIsByteStable()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}{SourceId}/source.toml";
        var atomPath = $"{BackfillInventoryLoader.RootPath}{SourceId}/absorbed-closed/{AtomId}.yaml";
        var raw = RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText(sourcePath, CanonicalSourceMetadataText()),
            RawRepositoryEntry.FromText(atomPath, CanonicalAtomText()),
        ]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var entry = Assert.Single(BackfillInventoryLoader.Load(snapshot).RequireDigestionEntries());

        var rewritten = BackfillInventoryWriter.WriteAtom(entry);

        Assert.Equal(Encoding.UTF8.GetBytes(CanonicalAtomText()), rewritten.ToArray());
    }

    [Fact]
    public void StatusAuthorityIdentity_IsOrderInsensitive()
    {
        var canonical = Entry(CanonicalCoverage());
        var reordered = Entry(
            [
                new DigestionCoverageEdge(ZetaGid, ZetaTargetHash),
                new DigestionCoverageEdge(AlphaGid, AlphaTargetHash),
            ]);
        var source = new DigestionLedgerSource(
            SourceId,
            SourcePath,
            AtomizerRegistry.NoAtomizerId,
            [],
            GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
            []);

        var canonicalIdentity = BackfillInventoryWriter.WriteStatusAuthorityIdentity(source, canonical);
        var reorderedIdentity = BackfillInventoryWriter.WriteStatusAuthorityIdentity(source, reordered);

        Assert.Equal(canonicalIdentity.ToArray(), reorderedIdentity.ToArray());
    }

    private static DigestionLedgerEntry Entry(
        ImmutableArray<DigestionCoverageEdge> coverage) =>
        new(
            SourceId,
            SourcePath,
            AtomizerRegistry.NoAtomizerId,
            AtomId,
            new DigestionFingerprints(RawHash, NormalizedHash),
            coverage,
            new DigestionReceipts([], [], null),
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            RawHash);

    private static ImmutableArray<DigestionCoverageEdge> CanonicalCoverage() =>
    [
        new DigestionCoverageEdge(AlphaGid, AlphaTargetHash),
        new DigestionCoverageEdge(ZetaGid, ZetaTargetHash),
    ];

    private static string CanonicalSourceMetadataText() => $$"""
        source_id = "{{SourceId}}"
        path = "{{SourcePath}}"
        atomizer = "{{AtomizerRegistry.NoAtomizerId}}"
        genre_registry_check = "no-registry"
        unregistered_genres = []
        """ + "\n";

    private static string CanonicalAtomText() => $$"""
        fingerprints:
          raw_sha256: {{RawHash}}
          normalized_sha256: {{NormalizedHash}}
        cas_ref: {{RawHash}}
        coverage_gids:
          - gid: {{AlphaGid}}
            target_statement_id: {{AlphaTargetHash}}
          - gid: {{ZetaGid}}
            target_statement_id: {{ZetaTargetHash}}
        receipts:
          unresolved_subitems: []
        """ + "\n";
}
