using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    private static ImmutableHashSet<string> RecoverableDuplicatePaths(
        RawRepositorySnapshot currentRaw,
        BackfillInventoryDocument currentDocument,
        ImmutableHashSet<string>? selectedSourceIds)
    {
        ArgumentNullException.ThrowIfNull(currentRaw);
        ArgumentNullException.ThrowIfNull(currentDocument);

        var currentPaths = currentRaw.Entries
            .Select(static entry => entry.Path)
            .ToHashSet(StringComparer.Ordinal);
        var selected = selectedSourceIds
            ?? currentDocument.RequireDigestionSources()
                .Select(static source => source.SourceId)
                .ToImmutableHashSet(StringComparer.Ordinal);
        var recovered = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);

        foreach (var group in currentDocument.RequireDigestionEntries()
                     .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
                     .Where(static group => group.Count() > 1))
        {
            var occurrences = group.ToArray();
            if (occurrences.Length != 2
                || occurrences.Select(static entry => entry.SourceId).Distinct(StringComparer.Ordinal).Count() != 1)
            {
                throw UnsupportedDuplicate(group.Key, "competing source occurrences");
            }

            var sourceId = occurrences[0].SourceId;
            if (!selected.Contains(sourceId))
            {
                throw UnsupportedDuplicate(group.Key, "duplicate is outside selected source scope");
            }

            if (!SameSourceIdentity(occurrences[0], occurrences[1]))
            {
                throw UnsupportedDuplicate(group.Key, "source identity, fingerprints, or CAS differ");
            }

            var open = occurrences.Where(IsRecoverableOpen).ToArray();
            var covered = occurrences.Where(IsRecoverableCovered).ToArray();
            if (open.Length != 1 || covered.Length != 1)
            {
                throw UnsupportedDuplicate(group.Key, "coverage, status, or receipts do not form one open/covered pair");
            }

            var openPath = NewAtomPath(open[0]);
            var coveredPath = NewAtomPath(covered[0]);
            if (!currentPaths.Contains(openPath) || !currentPaths.Contains(coveredPath))
            {
                throw UnsupportedDuplicate(group.Key, "canonical occurrence path is missing");
            }

            recovered.Add(openPath);
        }

        return recovered.ToImmutable();
    }

    private static bool SameSourceIdentity(
        DigestionLedgerEntry left,
        DigestionLedgerEntry right) =>
        string.Equals(left.SourceId, right.SourceId, StringComparison.Ordinal)
        && string.Equals(left.SourcePath, right.SourcePath, StringComparison.Ordinal)
        && string.Equals(left.Atomizer, right.Atomizer, StringComparison.Ordinal)
        && left.Fingerprints == right.Fingerprints
        && string.Equals(left.CasRef, right.CasRef, StringComparison.Ordinal);

    private static bool IsRecoverableOpen(DigestionLedgerEntry entry) =>
        entry.ProjectedStatus == new DigestionStatus(
            DigestionMigrationState.Residual,
            DigestionTruthState.Open)
        && entry.Coverage.IsEmpty
        && entry.Receipts.IsEmpty;

    private static bool IsRecoverableCovered(DigestionLedgerEntry entry) =>
        entry.ProjectedStatus == new DigestionStatus(
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed)
        && !entry.Coverage.IsEmpty
        && entry.Receipts.IsEmpty;

    private static RawRepositorySnapshot RemoveRecoveredPaths(
        RawRepositorySnapshot raw,
        ImmutableHashSet<string> recoveryPaths) =>
        recoveryPaths.IsEmpty
            ? raw
            : RawRepositorySnapshot.Create(
                raw.Entries.Where(entry => !recoveryPaths.Contains(entry.Path)),
                raw.PathInventory);

    private static InvalidOperationException UnsupportedDuplicate(string atomId, string reason) =>
        new($"ingest cannot recover duplicate atom id {atomId}: {reason}");
}
