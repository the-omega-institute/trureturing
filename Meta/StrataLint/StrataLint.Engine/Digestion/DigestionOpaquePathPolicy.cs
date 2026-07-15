namespace StrataLint.Engine;

internal static class DigestionOpaquePathPolicy
{
    internal const string TheoryRootPath = "docs/develop/theory/";

    internal static bool IsOpaque(RepoPath path) =>
        path.Value.StartsWith(TheoryRootPath, StringComparison.Ordinal)
        || DigestionCasStore.IsCanonicalPath(path.Value);
}
