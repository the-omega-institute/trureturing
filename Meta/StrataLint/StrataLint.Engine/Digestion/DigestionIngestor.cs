using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record DigestionIngestPlan(
    BackfillInventoryDocument Document,
    int StaleAcknowledged,
    int ResidualOpenAdded,
    ImmutableArray<DigestionCasObject> CasObjects,
    ImmutableArray<DigestionIngestFallback> Fallbacks);

internal static class DigestionIngestor
{
    internal static DigestionIngestPlan Plan(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument baselineDocument)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(baselineDocument);

        var migrationDocument = PrepareLegacyMigrations(document);
        var alignment = DigestionLedgerAligner.Evaluate(
            migrationDocument,
            snapshot,
            baselineDocument,
            DigestionAlignmentMode.Ingest);
        if (alignment.Findings.Length > 0)
        {
            throw new FormatException(
                "ingest alignment is invalid: " + string.Join("; ", alignment.Findings));
        }

        var stale = alignment.ActualStale.ToHashSet(StringComparer.Ordinal);
        var residualBySource = alignment.Residual
            .GroupBy(static item => item.SourceId, StringComparer.Ordinal)
            .ToDictionary(static group => group.Key, static group => group.ToArray(), StringComparer.Ordinal);
        var atomIds = migrationDocument.RequireDigestionEntries()
            .Select(static entry => entry.AtomId)
            .ToHashSet(StringComparer.Ordinal);
        var sources = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        var casObjects = new Dictionary<string, DigestionCasObject>(StringComparer.Ordinal);
        var staleAcknowledged = 0;
        var residualOpenAdded = 0;
        foreach (var source in migrationDocument.RequireDigestionSources())
        {
            if (!AtomizerRegistry.IsRegistered(source.Atomizer))
            {
                if (source.Atomizer != AtomizerRegistry.NoAtomizerId)
                {
                    throw new FormatException($"ingest source {source.SourceId} has unknown atomizer {source.Atomizer}");
                }

                sources.Add(CaptureBoundarySource(source, snapshot, casObjects));
                continue;
            }

            if (!source.Entries.Any(static entry => entry.Boundary is null))
            {
                sources.Add(source);
                continue;
            }

            var acknowledgments = source.Entries
                .Where(entry => stale.Contains(entry.AtomId))
                .Select(static entry => entry.AtomId)
                .Order(StringComparer.Ordinal)
                .ToImmutableArray();
            var priorAcknowledgments = source.AcknowledgedStale.ToHashSet(StringComparer.Ordinal);
            staleAcknowledged += acknowledgments.Count(priorAcknowledgment =>
                !priorAcknowledgments.Contains(priorAcknowledgment));
            var entries = source.Entries
                .Select(entry => CaptureMatchedAtom(entry, alignment, casObjects))
                .ToImmutableArray()
                .ToBuilder();
            if (residualBySource.TryGetValue(source.SourceId, out var residual))
            {
                foreach (var item in residual)
                {
                    if (!atomIds.Add(item.SuggestedAtomId))
                    {
                        throw new FormatException(
                            $"ingest residual atom_id collides with the ledger: {item.SuggestedAtomId}");
                    }

                    var captured = AddCasObject(item.Atom.RawBytes.AsSpan(), casObjects);
                    entries.Add(new DigestionLedgerEntry(
                        source.SourceId,
                        source.SourcePath,
                        source.Atomizer,
                        item.SuggestedAtomId,
                        item.Atom.AstPath,
                        Boundary: null,
                        item.Atom.Fingerprints,
                        CoverageGids: [],
                        new DigestionReceipts([], [], [], [], null),
                        item.ProjectedStatus,
                        ReceiptSyntax: null,
                        CasRef: captured.Reference));
                    residualOpenAdded++;
                }
            }

            sources.Add(source with
            {
                AcknowledgedStale = acknowledgments,
                Entries = entries.ToImmutable(),
            });
        }

        return new DigestionIngestPlan(
            migrationDocument.WithDigestionSources(sources.ToImmutable()),
            staleAcknowledged,
            residualOpenAdded,
            casObjects.Values
                .OrderBy(static item => item.RelativePath, StringComparer.Ordinal)
                .ToImmutableArray(),
            alignment.Fallbacks);
    }

    private static DigestionLedgerSource CaptureBoundarySource(
        DigestionLedgerSource source,
        RepositorySnapshot snapshot,
        IDictionary<string, DigestionCasObject> casObjects)
    {
        if (!snapshot.TryGetFile(source.SourcePath, out var sourceFile))
        {
            throw new FormatException($"ingest source path is dangling: {source.SourcePath}");
        }

        return source with
        {
            Entries = source.Entries
                .Select(entry => CaptureBoundaryEntry(entry, sourceFile.RawBytes, casObjects))
                .ToImmutableArray(),
        };
    }

    private static DigestionLedgerEntry CaptureBoundaryEntry(
        DigestionLedgerEntry entry,
        ImmutableArray<byte> sourceBytes,
        IDictionary<string, DigestionCasObject> casObjects)
    {
        if (entry.CasRef is not null)
        {
            return entry;
        }

        var boundary = entry.Boundary
            ?? throw new FormatException($"ingest no-atomizer entry {entry.AtomId} has no boundary");
        if (boundary.StartByte < 0
            || boundary.EndByte <= boundary.StartByte
            || boundary.EndByte > sourceBytes.Length)
        {
            throw new FormatException($"ingest entry {entry.AtomId} boundary is outside {entry.SourcePath}");
        }

        var bytes = sourceBytes.AsSpan()[boundary.StartByte..boundary.EndByte];
        if (DigestionFingerprint.Compute(bytes) != entry.Fingerprints)
        {
            throw new FormatException($"ingest entry {entry.AtomId} boundary fingerprint mismatch");
        }

        var captured = AddCasObject(bytes, casObjects);
        return entry with
        {
            CasRef = captured.Reference,
            ReceiptSyntax = null,
        };
    }

    private static DigestionLedgerEntry CaptureMatchedAtom(
        DigestionLedgerEntry entry,
        DigestionLedgerAlignment alignment,
        IDictionary<string, DigestionCasObject> casObjects)
    {
        if (entry.CasRef is not null
            || !alignment.MatchedAtoms.TryGetValue(entry.AtomId, out var atom)
            || atom.Fingerprints.RawSha256 != entry.Fingerprints.RawSha256)
        {
            return entry;
        }

        var captured = AddCasObject(atom.RawBytes.AsSpan(), casObjects);
        if (captured.Reference != entry.Fingerprints.RawSha256)
        {
            throw new FormatException(
                $"ingest CAS hash disagrees with entry {entry.AtomId} raw fingerprint");
        }

        return entry with
        {
            CasRef = captured.Reference,
            ReceiptSyntax = null,
        };
    }

    private static DigestionCasObject AddCasObject(
        ReadOnlySpan<byte> bytes,
        IDictionary<string, DigestionCasObject> casObjects)
    {
        var captured = DigestionCasStore.Capture(bytes);
        if (casObjects.TryGetValue(captured.Reference, out var existing))
        {
            if (!existing.Bytes.AsSpan().SequenceEqual(captured.Bytes.AsSpan()))
            {
                throw new FormatException($"ingest CAS collision at {captured.Reference}");
            }

            return existing;
        }

        casObjects.Add(captured.Reference, captured);
        return captured;
    }

    private static BackfillInventoryDocument PrepareLegacyMigrations(
        BackfillInventoryDocument document) =>
        document.WithDigestionSources(document.RequireDigestionSources()
            .Select(source => !AtomizerRegistry.IsRegistered(source.Atomizer)
                ? source
                : source with
                {
                    Entries = source.Entries
                        .Select(static entry => entry.Boundary is null
                            ? entry
                            : entry with
                            {
                                Boundary = null,
                                ReceiptSyntax = null,
                            })
                        .ToImmutableArray(),
                })
            .ToImmutableArray());
}
