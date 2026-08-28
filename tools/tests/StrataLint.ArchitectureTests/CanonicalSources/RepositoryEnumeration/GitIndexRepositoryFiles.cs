namespace StrataLint.ArchitectureTests;

internal static class GitIndexRepositoryFiles
{
    internal static IReadOnlyList<(string RelativePath, string FullPath)> Enumerate(
        string repositoryRoot) => StrataLint.Engine.GitIndexRepositoryFiles.Enumerate(repositoryRoot);

    /// <summary>
    /// 声明式仓库枚举:只返回 <paramref name="declaredPrefix"/> 之下的 tracked 文件,
    /// 并让 <c>ScribeTestMapDeriver</c> 把该前缀登记为本测试方法的 declared input。
    ///
    /// **为什么需要它**:`GitIndexRepositoryFiles.Enumerate` 读 git index,不触发
    /// `DirectoryEnumeration` unknown —— 但它也**不声明任何输入路径**,于是
    /// `EngineeringTestPlanDeriver` 在只改该前缀下文件的 PR 上不会选中调用它的测试。
    /// 一次评审用「临时克隆只加一条 D5 .lean → planner 输出 `cold_build_observer=[]`」
    /// 实测出这个缺口(#2535 / PR #3799 第二轮)。
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
