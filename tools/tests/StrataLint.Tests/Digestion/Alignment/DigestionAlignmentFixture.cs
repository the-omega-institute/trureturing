using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    internal static BackfillInventoryDocument Ledger(
        IReadOnlyList<string> acknowledgedStale,
        params DigestionLedgerEntry[] entries) =>
        LedgerForPath("docs/source.md", acknowledgedStale, entries);

    internal static BackfillInventoryDocument LedgerForPath(
        string sourcePath,
        IReadOnlyList<string> acknowledgedStale,
        params DigestionLedgerEntry[] entries) =>
        BackfillInventoryDocument.Create(
        [
            new DigestionLedgerSource(
                "source",
                sourcePath,
                AtomizerRegistry.GictId,
                acknowledgedStale.ToImmutableArray(),
                GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
                entries.ToImmutableArray()),
        ],
        []);

    internal static DigestionLedgerEntry Entry(string atomId, DigestionAtom atom) =>
        EntryForPath(atomId, atom.AstPath, atom.Fingerprints);

    private static DigestionLedgerEntry CasEntry(
        string atomId,
        DigestionAtom atom,
        string casRef) =>
        EntryForPath(atomId, atom.AstPath, atom.Fingerprints) with { CasRef = casRef };

    private static DigestionLedgerEntry BoundaryEntry(string atomId, DigestionAtom atom) =>
        Entry(atomId, atom) with
        {
            Boundary = new DigestionBoundary(atom.AstPath, atom.StartByte, atom.EndByte),
        };

    private static DigestionLedgerEntry EntryForPath(
        string atomId,
        string astPath,
        DigestionFingerprints fingerprints) => new(
            "source",
            "docs/source.md",
            AtomizerRegistry.GictId,
            atomId,
            astPath,
            null,
            fingerprints,
            [],
            new DigestionReceipts([], [], [], [], null),
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            fingerprints.RawSha256);

    internal static BackfillInventoryDocument WithAtomizer(
        BackfillInventoryDocument document,
        string atomizer)
    {
        var source = Assert.Single(document.RequireDigestionSources());
        return document.WithDigestionSources(
        [
            source with
            {
                Atomizer = atomizer,
                Entries = source.Entries
                    .Select(entry => entry with { Atomizer = atomizer })
                    .ToImmutableArray(),
            },
        ]);
    }

    internal static BackfillInventoryDocument WithSourceId(
        BackfillInventoryDocument document,
        string sourceId)
    {
        var source = Assert.Single(document.RequireDigestionSources());
        return document.WithDigestionSources(
        [
            source with
            {
                SourceId = sourceId,
                Entries = source.Entries
                    .Select(entry => entry with { SourceId = sourceId })
                    .ToImmutableArray(),
            },
        ]);
    }

}
