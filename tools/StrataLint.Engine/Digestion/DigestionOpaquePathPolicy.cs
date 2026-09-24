namespace StrataLint.Engine;

internal static class DigestionOpaquePathPolicy
{
    internal const string TheoryRootPath = "docs/develop/theory/";

    // Theory isolation is structural; FILEMAP separately owns membership and source eligibility.
    internal static bool IsTheoryDocument(RepoPath path) =>
        path.Value.StartsWith(TheoryRootPath, StringComparison.Ordinal);

    internal static bool IsOpaque(RepoPath path) =>
        path.Value.StartsWith(TheoryRootPath, StringComparison.Ordinal)
        || path.Value == TheoryAtomizerDataLoader.DataPath
        || DigestionCasStore.IsCanonicalPath(path.Value);
}
