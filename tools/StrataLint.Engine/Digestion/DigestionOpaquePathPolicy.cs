namespace StrataLint.Engine;

internal static class DigestionOpaquePathPolicy
{
    internal const string TheoryRootPath = "docs/develop/theory/";

    internal static bool IsOpaque(RepoPath path) =>
        path.Value.StartsWith(TheoryRootPath, StringComparison.Ordinal)
        || path.Value == TheoryAtomizerDataLoader.DataPath
        || DigestionCasStore.IsCanonicalPath(path.Value);
}
