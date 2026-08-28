namespace StrataLint.ArchitectureTests;

/// <summary>
/// #2535 的 `policy-override` 声明自己「**非永久**」。本类是那句声明的观察者。
/// </summary>
public sealed class ColdBuildBudgetReviewLineTests
{
    /// <summary>
    /// 该 override 的复审触发线是 D5 内容层模块数达到
    /// <see cref="StrataLint.Cli.LeanCacheBudgetPolicy.ColdBuildBudgetReviewModuleCount"/>
    /// (由 #3029 裁定:本机实测 3388s / 1571 模块的单模块冷建成本 × 预算的 80% 线)。
    /// **在本类之前那条线没有任何观察者** —— 2026-08-26 实测 `grep -rnw 2672` 全仓 0 命中,
    /// 阳性对照 `grep -rnw 7200` 得 7 条,证明探针有效,故那个 0 是阴性证据而非坏探针。
    ///
    /// 而它正在被逼近:同一实测里 D5 是 2033;两天后是 2466。该量单调不减(冻结律),
    /// 故必然跨过 —— 「必然为真」不等于「有人看见」。
    ///
    /// **为什么用 <see cref="GitIndexRepositoryFiles"/> 而不是目录枚举**:
    /// `ScribeTestMapDeriver` 对任何 `EnumerateFiles` 调用无条件记
    /// `TestMapUnknownReason.DirectoryEnumeration`,新增即撞 unknown 棘轮
    /// (本条的第一版正是这样被 admission 判红的:
    /// `conservative unknown test method introduced after fork point`)。
    /// git index 口径与 `find D5 -name '*.lean' | wc -l` 在 2026-08-28 实测同为 2466,
    /// 且 D5 下未跟踪 `.lean` 为 0,故两口径此刻不可分。
    ///
    /// **红了怎么办**:不要改那个数让它变绿 —— 那是把到期的期票撕掉。
    /// 按 #2535 重新把预算收口到三型之一,或按 #3029 的五条开建条件建拦全量冷建的门,
    /// 然后连同本测试一并重写。触发线取 80% 而非 100%,正是为了让红出现时**预算仍够用**。
    /// </summary>
    [Fact]
    public void ColdBuildBudgetReviewLineHasNotBeenCrossed()
    {
        var modules = GitIndexRepositoryFiles
            .Enumerate(RepositoryLayout.FindRoot())
            .Count(file => file.RelativePath.StartsWith("D5/", StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".lean", StringComparison.Ordinal));

        Assert.True(
            modules < StrataLint.Cli.LeanCacheBudgetPolicy.ColdBuildBudgetReviewModuleCount,
            $"D5 内容层已有 {modules} 个模块,达到或越过 #3029 裁定的复审触发线 "
            + $"{StrataLint.Cli.LeanCacheBudgetPolicy.ColdBuildBudgetReviewModuleCount}:"
            + "全量冷建的预计耗时已越过 "
            + $"{StrataLint.Cli.LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds}s 预算的 80% 线,"
            + "该 policy-override 的取值依据失效,其「非永久」声明到期。"
            + "按 https://github.com/the-omega-institute/trureturing/issues/2535 重新按三型收口,"
            + "或按 #3029 的五条开建条件建拦全量冷建的门。不要改那个数让本测试变绿。");
    }
}
