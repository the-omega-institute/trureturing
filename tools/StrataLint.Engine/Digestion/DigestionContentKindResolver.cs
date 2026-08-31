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

        return result.ToImmutable();
    }
}
