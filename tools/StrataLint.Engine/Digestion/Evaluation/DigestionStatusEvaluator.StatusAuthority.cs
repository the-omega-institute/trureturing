using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class DigestionStatusEvaluator
{
    internal static ImmutableHashSet<string> StatusAuthorityChangedAtomIds(
        BackfillInventoryDocument document,
        RawChangeSet? changes,
        DigestionLedgerAlignment alignment)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(alignment);
        return ResolveStatusAuthorityChangedAtomIds(
            document.RequireDigestionEntries(),
            changes,
            alignment,
            isBaseFactAffected: null);
    }

    private static ImmutableHashSet<string> ResolveStatusAuthorityChangedAtomIds(
        IEnumerable<DigestionLedgerEntry> sourceEntries,
        RawChangeSet? changes,
        DigestionLedgerAlignment alignment,
        Func<string, bool>? isBaseFactAffected)
    {
        var entries = sourceEntries.ToArray();
        var directlyChanged = entries
            .Where(entry => StatusAuthorityClosureChanged(
                entry,
                alignment.EntryAlignments.GetValueOrDefault(
                    entry.AtomId,
                    DigestionReceiptAlignment.Rejected),
                changes,
                isBaseFactAffected))
            .Select(static entry => entry.AtomId);
        return ExpandStatusAuthorityChanges(entries, directlyChanged);
    }

    private static ImmutableHashSet<string> ExpandStatusAuthorityChanges(
        IEnumerable<DigestionLedgerEntry> sourceEntries,
        IEnumerable<string> initiallyChanged)
    {
        var entries = sourceEntries.ToArray();
        var atomIds = entries.Select(static entry => entry.AtomId).ToHashSet(StringComparer.Ordinal);
        var changedAtomIds = initiallyChanged.ToHashSet(StringComparer.Ordinal);
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var entry in entries.Where(entry => !changedAtomIds.Contains(entry.AtomId)))
            {
                if (entry.Receipts.ChainAtoms.Any(atomId =>
                        atomIds.Contains(atomId) && changedAtomIds.Contains(atomId)))
                {
                    changedAtomIds.Add(entry.AtomId);
                    changed = true;
                }
            }
        }

        return changedAtomIds.ToImmutableHashSet(StringComparer.Ordinal);
    }
}
