using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    internal const int LibraryDocumentLineLimit = 3000;

    private static bool IsLibraryDocument(string path) =>
        path.StartsWith("Library/", StringComparison.Ordinal)
        && path.EndsWith(".md", StringComparison.OrdinalIgnoreCase);

    private static ImmutableArray<RuleFinding> LibraryCapacity(RepositorySnapshot current, RawChangeSet changes)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var change in changes.Entries.Where(static change =>
            change.Kind is RawChangeKind.Added or RawChangeKind.Modified
            && IsLibraryDocument(change.Path.Value)))
        {
            if (!current.Files.TryGetValue(change.Path, out var file))
                continue;

            var lines = CountArtifactLines(file.Text);
            if (lines > LibraryDocumentLineLimit)
                findings.Add(new(change.Path.Value,
                    $"library document spans {lines} lines (hard limit {LibraryDocumentLineLimit}); "
                    + "split material into separate notes and link related notes"));
        }

        return findings.ToImmutable();
    }
}
