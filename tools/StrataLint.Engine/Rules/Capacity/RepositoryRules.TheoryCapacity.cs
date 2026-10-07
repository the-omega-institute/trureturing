using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    internal const int TheoryDocumentLineLimit = 5000;

    private static bool IsTheoryDocument(string path) =>
        path.StartsWith(DigestionOpaquePathPolicy.TheoryRootPath, StringComparison.Ordinal)
        && path.EndsWith(".md", StringComparison.OrdinalIgnoreCase);

    private static ImmutableArray<RuleFinding> TheoryCapacity(DeltaRuleContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var change in context.Changes.Entries.Where(static change =>
            change.Kind is RawChangeKind.Added or RawChangeKind.Modified
            && IsTheoryDocument(change.Path.Value)))
        {
            var path = change.Path;
            if (!context.Current.Files.TryGetValue(path, out var file))
                continue;

            // Theory inputs remain opaque; count line separators in the original bytes.
            var bytes = file.RawBytes.AsSpan();
            var lines = bytes.Count((byte)'\n')
                + (!bytes.IsEmpty && bytes[^1] != (byte)'\n' ? 1 : 0);
            if (lines > TheoryDocumentLineLimit)
                findings.Add(new(path.Value,
                    $"theory document spans {lines} lines (hard limit {TheoryDocumentLineLimit}); "
                    + "continue in a separate volume and preserve existing entries and references"));
        }

        return findings.ToImmutable();
    }
}
