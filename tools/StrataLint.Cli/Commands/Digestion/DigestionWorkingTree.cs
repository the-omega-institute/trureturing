using StrataLint.Engine;

namespace StrataLint.Cli;

// Loads explicit source, CAS, and Lean inputs for a selected mutation.
internal static class DigestionWorkingTree
{
    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) Extend(
        IRepositoryGateway repository,
        (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) current,
        Func<RawRepositorySnapshot, RepositorySnapshot> decode,
        params string[] additional)
    {
        ArgumentNullException.ThrowIfNull(current.Raw);
        var present = current.Raw.Entries
            .Select(static entry => entry.Path)
            .ToHashSet(StringComparer.Ordinal);
        var missing = additional
            .Where(path => !present.Contains(path))
            .Distinct(StringComparer.Ordinal)
            .ToArray();
        if (missing.Length == 0)
        {
            return current;
        }

        var extra = repository.ReadCurrent(missing);
        if (extra.Entries.Any(static entry => BackfillInventoryLoader.IsCanonicalPath(entry.Path)
                || entry.Path == BackfillInventoryLoader.RelativePath))
            throw new InvalidOperationException("digestion input extension must not add ledger files");
        var merged = RawRepositorySnapshot.Create(current.Raw.Entries
            .Concat(extra.Entries)
            .DistinctBy(static entry => entry.Path, StringComparer.Ordinal)
            .OrderBy(static entry => entry.Path, StringComparer.Ordinal));
        var decoded = decode(merged);
        return (merged, decoded, current.Document);
    }

    // A source context only needs CAS objects reachable through persisted chains.
    // Leaf atoms are reconstructed from the source atomizer and do not need their
    // duplicated CAS bytes in the query snapshot.
    internal static string[] ChainCasPaths(
        BackfillInventoryDocument document,
        IEnumerable<string> roots)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(roots);
        // Keep malformed duplicate identities in the ledger for the command's
        // domain validation.  They must not escape as a generic Dictionary
        // exception before the caller can report the expected occurrence error.
        var entries = document.RequireDigestionEntries()
            .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .Where(static group => group.Count() == 1)
            .ToDictionary(static group => group.Key, static group => group.Single(), StringComparer.Ordinal);
        var ids = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Queue<string>(roots);
        while (pending.TryDequeue(out var id))
        {
            if (!DigestionNonpropositional.IsAtomId(id) || !ids.Add(id)) continue;
            if (!entries.TryGetValue(id, out var entry)) continue;
            foreach (var childId in entry.Receipts.ChainAtoms)
                pending.Enqueue(childId);
        }

        return ids
            .Select(static id => DigestionCasStore.RootPath + id)
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

}
