using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class DigestionContentKindResolver
{
    internal static ImmutableDictionary<string, string> Resolve(
        RepositorySnapshot snapshot,
        BackfillInventoryDocument ledger)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(ledger);
        var rules = TheoryAtomizerDataLoader.Load(snapshot);
        var result = ImmutableDictionary.CreateBuilder<string, string>(StringComparer.Ordinal);

        foreach (var source in ledger.RequireDigestionSources())
        {
            if (string.Equals(source.Atomizer, AtomizerRegistry.NoAtomizerId, StringComparison.Ordinal))
            {
                continue;
            }

            if (!snapshot.TryGetFile(source.SourcePath, out var sourceFile))
            {
                throw new FormatException(
                    $"source {source.SourceId} content is missing: {source.SourcePath}");
            }

            var kindsByHash = AtomizerRegistry.ResolveContentKinds(
                source.Atomizer,
                sourceFile.RawBytes.AsSpan(),
                rules);
            foreach (var entry in source.Entries)
            {
                if (!kindsByHash.TryGetValue(entry.Fingerprints.RawSha256, out var kind))
                {
                    continue;
                }

                if (!result.TryAdd(entry.AtomId, kind))
                {
                    throw new FormatException($"duplicate atom_id: {entry.AtomId}");
                }
            }
        }

        var entries = ledger.RequireDigestionEntries().ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
        var sourceKinds = result.ToImmutable();
        var pending = new Queue<string>(result.Keys.Order(StringComparer.Ordinal));
        var visited = new HashSet<string>(StringComparer.Ordinal);
        while (pending.TryDequeue(out var id))
        {
            if (!visited.Add(id) || !entries.TryGetValue(id, out var parent)
                || parent.Receipts.ChainAtoms.IsEmpty
                || parent.Receipts.ChainAtoms.All(sourceKinds.ContainsKey)) continue;
            if (!snapshot.TryGetFile(DigestionCasStore.RootPath + id, out var blob))
                throw new FormatException($"parent CAS blob is missing: {id}");
            var plan = DigestionDecomposition.Plan(parent, blob.RawBytes,
                AtomizerRegistry.Require(parent.Atomizer).Atomize, rules, snapshot);
            if (!plan.IsExplicit && sourceKinds.ContainsKey(id)) continue;
            var materialized = DigestionDecomposition.Materialize(parent, plan, entries);
            if (!materialized.NewEntries.IsEmpty)
                throw new FormatException($"chain atom is absent for parent {id}");
            foreach (var childId in parent.Receipts.ChainAtoms)
            {
                if (entries[childId].SourceId != parent.SourceId || sourceKinds.ContainsKey(childId)) continue;
                if (result.TryGetValue(childId, out var kind) && kind != result[id])
                    throw new FormatException($"CONTENT_KIND_CONFLICT atom_id={childId}");
                if (!result.ContainsKey(childId)) result.Add(childId, result[id]);
                pending.Enqueue(childId);
            }
        }
        return result.ToImmutable();
    }
}
