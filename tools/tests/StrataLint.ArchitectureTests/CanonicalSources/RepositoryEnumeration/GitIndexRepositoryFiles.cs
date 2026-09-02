namespace StrataLint.ArchitectureTests;

internal static class GitIndexRepositoryFiles
{
    internal static IReadOnlyList<(string RelativePath, string FullPath)> Enumerate(
        string repositoryRoot) => StrataLint.Engine.GitIndexRepositoryFiles.Enumerate(repositoryRoot);

    /// <summary>
    /// 声明式仓库枚举:只返回 <paramref name="declaredPrefix"/> 之下的 tracked 文件,
    /// 并让 <c>ScribeTestMapDeriver</c> 把该前缀登记为本测试方法的 declared input。
    ///
    /// `declaredPrefix` **必须是字面量**;传变量时 deriver 会 fail-closed 记 `VariablePath`。
    /// </summary>
    internal static IReadOnlyList<(string RelativePath, string FullPath)> EnumerateDeclared(
        string repositoryRoot,
        string declaredPrefix) =>
        StrataLint.Engine.GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(file => file.RelativePath.StartsWith(declaredPrefix + "/", StringComparison.Ordinal))
            .ToArray();
}
