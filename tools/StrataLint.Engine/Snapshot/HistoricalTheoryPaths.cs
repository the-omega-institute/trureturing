namespace StrataLint.Engine;

internal static class HistoricalTheoryPaths
{
    internal const string TheoryRootPath = "docs/develop/theory/";

    // Historical snapshots can contain opaque source text and binary CAS blobs.
    internal static bool IsTheoryDocument(RepoPath path) =>
        path.Value.StartsWith(TheoryRootPath, StringComparison.Ordinal);

    internal static bool IsAuxiliaryData(RepoPath path) =>
        IsTheoryDocument(path)
        || path.Value.StartsWith("Meta/Digestion/backfill/", StringComparison.Ordinal)
        || path.Value.StartsWith("Meta/Digestion/atoms/", StringComparison.Ordinal)
        || path.Value == "Meta/BACKFILL.yaml";

    internal static bool IsOpaque(RepoPath path) =>
        path.Value.StartsWith(TheoryRootPath, StringComparison.Ordinal)
        || path.Value.StartsWith("Meta/Digestion/atoms/sha256/", StringComparison.Ordinal)
            && FrozenHashSyntax.IsSha256("sha256:" + path.Value["Meta/Digestion/atoms/sha256/".Length..]);
}
