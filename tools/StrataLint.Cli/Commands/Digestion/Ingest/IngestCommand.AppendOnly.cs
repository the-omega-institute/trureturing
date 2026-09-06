using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    internal static void RequireAppendOnlyWriteSet(
        RawRepositorySnapshot currentRaw,
        BackfillInventoryDocument currentDocument,
        BackfillInventoryDocument finalDocument,
        ImmutableArray<LedgerUpdate> ledgerUpdates,
        ImmutableArray<DigestionCasObject> casObjects,
        ImmutableHashSet<string> newAtomIds,
        ImmutableHashSet<string>? sourceIds = null)
    {
        ArgumentNullException.ThrowIfNull(currentRaw);
        ArgumentNullException.ThrowIfNull(currentDocument);
        ArgumentNullException.ThrowIfNull(finalDocument);
        ArgumentNullException.ThrowIfNull(newAtomIds);
        var currentPaths = currentRaw.Entries
            .Select(static entry => entry.Path)
            .ToHashSet(StringComparer.Ordinal);
        var currentSourceIds = currentDocument.RequireDigestionSources()
            .Select(static source => source.SourceId)
            .ToHashSet(StringComparer.Ordinal);
        var currentAtomIds = currentDocument.RequireDigestionEntries()
            .Select(static entry => entry.AtomId)
            .ToHashSet(StringComparer.Ordinal);
        var finalSources = finalDocument.RequireDigestionSources()
            .ToDictionary(static source => source.SourceId, StringComparer.Ordinal);
        var finalEntriesByPath = finalDocument.RequireDigestionEntries()
            .ToDictionary(NewAtomPath, StringComparer.Ordinal);

        foreach (var update in ledgerUpdates)
        {
            if (update.Bytes is null || currentPaths.Contains(update.Path))
                throw WriteSetError(update.Path);

            var sourceMetadata = finalSources.Values.FirstOrDefault(source =>
                update.Path == $"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml");
            if (sourceMetadata is not null)
            {
                if (currentSourceIds.Contains(sourceMetadata.SourceId)
                    || sourceIds is not null && !sourceIds.Contains(sourceMetadata.SourceId))
                {
                    throw WriteSetError(update.Path);
                }
                continue;
            }

            if (!finalEntriesByPath.TryGetValue(update.Path, out var entry)
                || currentAtomIds.Contains(entry.AtomId)
                || !newAtomIds.Contains(entry.AtomId)
                || sourceIds is not null && !sourceIds.Contains(entry.SourceId)
                || entry.ProjectedStatus != new DigestionStatus(
                    DigestionMigrationState.Residual,
                    DigestionTruthState.Open)
                || !entry.Coverage.IsEmpty
                || !IsAllowedNewReceipt(entry.Receipts))
            {
                throw WriteSetError(update.Path);
            }
        }

        var newEntries = finalDocument.RequireDigestionEntries()
            .Where(entry => newAtomIds.Contains(entry.AtomId))
            .ToArray();
        var allowedReferences = newEntries
            .Select(static entry => entry.CasRef)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var captured in casObjects)
        {
            var recaptured = DigestionCasStore.Capture(captured.Bytes.AsSpan());
            if (!allowedReferences.Contains(captured.Reference)
                || recaptured.Reference != captured.Reference
                || recaptured.RelativePath != captured.RelativePath)
            {
                throw WriteSetError(captured.RelativePath);
            }
        }

        var updatePaths = ledgerUpdates.Select(static update => update.Path)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var entry in newEntries)
        {
            if (!updatePaths.Contains(NewAtomPath(entry)))
                throw WriteSetError(NewAtomPath(entry));
        }
    }

    internal static void RequireNewCasIntegrity(
        RawRepositorySnapshot currentRaw,
        BackfillInventoryDocument finalDocument,
        ImmutableArray<DigestionCasObject> casObjects,
        ImmutableHashSet<string> newAtomIds)
    {
        ArgumentNullException.ThrowIfNull(currentRaw);
        ArgumentNullException.ThrowIfNull(finalDocument);
        ArgumentNullException.ThrowIfNull(newAtomIds);
        var currentAtomIds = BackfillInventoryLoader.Load(Decode(currentRaw))
            .RequireDigestionEntries()
            .Select(static entry => entry.AtomId)
            .ToHashSet(StringComparer.Ordinal);
        var newEntries = finalDocument.RequireDigestionEntries()
            .Where(entry => newAtomIds.Contains(entry.AtomId))
            .ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
        if (newEntries.Count != newAtomIds.Count)
        {
            throw WriteSetError("new atom id set does not match final ledger entries");
        }

        var objects = casObjects.ToDictionary(static item => item.Reference, StringComparer.Ordinal);
        foreach (var (atomId, entry) in newEntries)
        {
            var expectedReference = "sha256:" + atomId;
            var expectedPath = DigestionCasStore.RootPath + atomId;
            if (currentAtomIds.Contains(atomId)
                || entry.Fingerprints.RawSha256 != expectedReference
                || entry.CasRef != expectedReference
                || !objects.TryGetValue(expectedReference, out var captured)
                || captured.RelativePath != expectedPath)
            {
                throw WriteSetError(expectedPath);
            }

            var recaptured = DigestionCasStore.Capture(captured.Bytes.AsSpan());
            if (recaptured.Reference != expectedReference
                || recaptured.RelativePath != expectedPath)
            {
                throw WriteSetError(expectedPath);
            }
        }
    }

    private static bool IsAllowedNewReceipt(DigestionReceipts receipts) =>
        receipts.Scribe.IsEmpty
        && receipts.UnresolvedSubitems.IsEmpty
        && receipts.TailAuthorization is null
        && receipts.Quarantine is null
        && receipts.CoverDisposition is null;

    private static InvalidOperationException WriteSetError(string path) =>
        new($"ingest append-only write set contains forbidden path: {path}");
}
