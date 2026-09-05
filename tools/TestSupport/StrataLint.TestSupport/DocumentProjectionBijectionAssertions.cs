namespace StrataLint.TestSupport;

internal static class DocumentProjectionBijectionAssertions
{
    internal static string[] MarkdownProjectionBijectionFindings(
        IEnumerable<string> requiredPaths,
        IEnumerable<string> actualPaths)
    {
        var required = requiredPaths.ToHashSet(StringComparer.Ordinal);
        var actual = actualPaths.ToHashSet(StringComparer.Ordinal);
        return required
            .Except(actual, StringComparer.Ordinal)
            .Select(static path => $"required Markdown projection is missing: {path}; "
                + $"run make emit and commit {path}")
            .Concat(actual
                .Except(required, StringComparer.Ordinal)
                .Select(static path => $"Markdown projection has no Scribe definition: {path}"))
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    internal static void AssertNoMarkdownProjectionBijectionFindings(
        IReadOnlyCollection<string> findings)
    {
        var completeMessage = string.Join(" | ", findings);
        Xunit.Assert.True(findings.Count == 0, completeMessage);
    }
}
