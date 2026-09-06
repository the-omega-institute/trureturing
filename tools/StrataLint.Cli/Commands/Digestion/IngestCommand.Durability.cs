using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    internal sealed record LedgerUpdate(
        string Path,
        ImmutableArray<byte>? Bytes,
        int DurabilityOrder = 0);

    private static string NewAtomPath(DigestionLedgerEntry entry) =>
        $"{BackfillInventoryLoader.RootPath}{entry.SourceId}/"
        + $"{DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)}-"
        + $"{DigestionStatusNames.Truth(entry.ProjectedStatus.Truth)}/{entry.AtomId}.yaml";

    internal static ImmutableArray<LedgerUpdate> LedgerUpdates(
        RawRepositorySnapshot current,
        RawRepositorySnapshot final,
        ImmutableHashSet<string>? sourceIds = null)
    {
        var currentEntries = current.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        var finalEntries = final.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        var currentRanks = LedgerDurabilityRanks(current);
        var finalRanks = LedgerDurabilityRanks(final);
        var updates = final.Entries
            .Where(static entry => entry.Path == BackfillInventoryLoader.RelativePath
                || BackfillInventoryLoader.IsCanonicalPath(entry.Path))
            .Where(entry => !currentEntries.TryGetValue(entry.Path, out var existing)
                || !existing.Bytes.AsSpan().SequenceEqual(entry.Bytes.AsSpan()))
            .Select(entry => new LedgerUpdate(
                entry.Path,
                entry.Bytes,
                finalRanks.GetValueOrDefault(entry.Path)))
            .Concat(current.Entries
                .Where(static entry => entry.Path == BackfillInventoryLoader.RelativePath
                    || BackfillInventoryLoader.IsCanonicalPath(entry.Path))
                .Where(entry => !finalEntries.ContainsKey(entry.Path))
                .Select(entry => new LedgerUpdate(
                    entry.Path,
                    null,
                    int.MaxValue - currentRanks.GetValueOrDefault(entry.Path))))
            .OrderBy(static update => update.DurabilityOrder)
            .ThenBy(static update => update.Path, StringComparer.Ordinal)
            .ToImmutableArray();
        if (sourceIds is not null)
        {
            var outside = updates.FirstOrDefault(update => !IsSelectedLedgerPath(update.Path, sourceIds));
            if (outside is not null)
                throw new InvalidOperationException($"ingest ledger write is outside selected sources: {outside.Path}");
        }
        return updates;
    }

    private static IReadOnlyDictionary<string, int> LedgerDurabilityRanks(
        RawRepositorySnapshot snapshot)
    {
        var document = LoadDocument(Decode(snapshot));
        var entries = document.RequireDigestionEntries().ToDictionary(
            static entry => entry.AtomId,
            StringComparer.Ordinal);
        var ranks = new Dictionary<string, int>(StringComparer.Ordinal);
        var visiting = new HashSet<string>(StringComparer.Ordinal);

        int Rank(string atomId)
        {
            if (ranks.TryGetValue(atomId, out var rank))
            {
                return rank;
            }

            if (!entries.TryGetValue(atomId, out var entry))
            {
                return 0;
            }

            if (!visiting.Add(atomId))
            {
                return 0;
            }

            rank = entry.Receipts.ChainAtoms.Length == 0
                ? 0
                : entry.Receipts.ChainAtoms.Max(Rank) + 1;
            visiting.Remove(atomId);
            ranks.Add(atomId, rank);
            return rank;
        }

        foreach (var atomId in entries.Keys)
        {
            Rank(atomId);
        }

        return entries.Values.ToDictionary(
            NewAtomPath,
            entry => ranks[entry.AtomId],
            StringComparer.Ordinal);
    }
}
