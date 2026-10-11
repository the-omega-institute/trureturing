using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    internal const int LibraryDocumentLineLimit = 3000;

    private static bool IsLibraryDocument(string path) =>
        path.StartsWith("Library/", StringComparison.Ordinal)
        && path.EndsWith(".md", StringComparison.OrdinalIgnoreCase);

    private static ImmutableArray<RuleFinding> LibraryCapacity(DeltaRuleContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var change in context.Changes.Entries.Where(static change =>
            change.Kind is RawChangeKind.Added && IsLibraryDocument(change.Path.Value)))
        {
            if (!context.Current.Files.TryGetValue(change.Path, out var file))
                continue;

            var lines = CountArtifactLines(file.Text);
            if (lines > LibraryDocumentLineLimit)
                findings.Add(new(change.Path.Value,
                    $"library document spans {lines} lines (hard limit {LibraryDocumentLineLimit}); "
                    + "split new material into separate notes and link related notes"));
        }

        return findings.ToImmutable();
    }
}
