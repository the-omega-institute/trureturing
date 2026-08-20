namespace StrataLint.Engine;

internal static class DigestionOpaquePathPolicy
{
    internal const string TheoryRootPath = "docs/develop/theory/";

    // 理论卷由**路径规则**判定,不由 registry.yaml 的枚举判定:第三方 PR 带进来的
    // 卷名无法预先枚举。此为该概念的唯一真源,路径策略与 backfill 规则共用。
    internal static bool IsTheoryDocument(RepoPath path) =>
        path.Value.StartsWith(TheoryRootPath, StringComparison.Ordinal);

    internal static bool IsOpaque(RepoPath path) =>
        path.Value.StartsWith(TheoryRootPath, StringComparison.Ordinal)
        || path.Value == TheoryAtomizerDataLoader.DataPath
        || DigestionCasStore.IsCanonicalPath(path.Value);
}
