using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static ImmutableArray<RuleFinding> ScribeNarrativeProvenance(DeltaRuleContext context)
    {
        // Keep this local: IsBaseFactAffected includes every file when the judge changes.
        var paths = context.Changes.Paths
            .Where(path => IsBlueprintPath(path.Value, ".scribe.cs") && context.Current.Files.ContainsKey(path))
            .ToImmutableArray();
        var moves = ScribeNarrativeMoves(context);
        return paths.Where(path => !moves.Contains(path))
            .SelectMany(path => ScribeNarrativeScanner.Scan(context.Current.Files[path].Text)
                .Select(finding => new RuleFinding(path.Value, finding.Message)))
            .ToImmutableArray();
    }

    private static ImmutableHashSet<RepoPath> ScribeNarrativeMoves(DeltaRuleContext context)
    {
        var comparer = new ScribeNarrativeByteComparer();
        var deleted = context.Changes.Entries
            .Where(entry => entry.Kind is RawChangeKind.Deleted
                && IsBlueprintPath(entry.Path.Value, ".scribe.cs")
                && context.Baseline.Files.ContainsKey(entry.Path))
            .GroupBy(entry => context.Baseline.Files[entry.Path].RawBytes, comparer)
            .ToDictionary(group => group.Key, group => group.Count(), comparer);
        // Ambiguous equal-byte groups are judged in full, including one deletion and two adds.
        return context.Changes.Entries
            .Where(entry => entry.Kind is RawChangeKind.Added
                && IsBlueprintPath(entry.Path.Value, ".scribe.cs")
                && context.Current.Files.ContainsKey(entry.Path))
            .GroupBy(entry => context.Current.Files[entry.Path].RawBytes, comparer)
            .Where(group => group.Count() == 1 && deleted.GetValueOrDefault(group.Key) == 1)
            .Select(group => group.Single().Path)
            .ToImmutableHashSet();
    }

    private sealed class ScribeNarrativeByteComparer : IEqualityComparer<ImmutableArray<byte>>
    {
        public bool Equals(ImmutableArray<byte> left, ImmutableArray<byte> right) =>
            left.AsSpan().SequenceEqual(right.AsSpan());

        public int GetHashCode(ImmutableArray<byte> bytes)
        {
            var hash = new HashCode();
            hash.AddBytes(bytes.AsSpan());
            return hash.ToHashCode();
        }
    }
}
