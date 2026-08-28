namespace StrataLint.ArchitectureTests;

/// <summary>
/// #2535 的 `policy-override` 声明自己「**非永久**」。本类是那句声明的观察者。
///
/// **本类的两条测试是分工的**:一条判「线有没有被跨过」,另一条判「那条线还在不在」。
/// 分开是因为一条评审判词实测出:只有前者时,把阈值抬到 `int.MaxValue`
/// 或把枚举模式拼错成 `"*.leam"`,**整套 36 个相关用例仍 36/36 全绿** —— 空守卫的教科书形态。
/// </summary>
public sealed class ColdBuildBudgetReviewLineTests
{
    /// <summary>
    /// 复审触发线由 #3029 裁定为 **2672**。本测试把它钉死。
    ///
    /// **为什么用字面量而不是引用那个常量**:本测试要防的正是「有人改那个常量让另一条测试变绿」,
    /// 若这里也引用它,两边一起变,断言恒真(本仓已记的「夹具里的值别名」)。
    /// 故这里的 `2672` 必须是独立写下的第二个来源。
    ///
    /// **红了怎么办**:若 #3029 的裁定被正式修订,改这里并在 PR 里引用那次修订;
    /// 若只是想让另一条测试变绿,**那正是本测试要拦的事**。
    /// </summary>
    [Fact]
    public void ColdBuildBudgetReviewLineIsPinnedToTheAdjudicatedValue()
    {
        Assert.Equal(2672, StrataLint.Cli.LeanCacheBudgetPolicy.ColdBuildBudgetReviewModuleCount);
    }

    /// <summary>
    /// D5 内容层模块数尚未达到
    /// <see cref="StrataLint.Cli.LeanCacheBudgetPolicy.ColdBuildBudgetReviewModuleCount"/>。
    ///
    /// **在本类之前那条线没有任何观察者** —— 2026-08-26 实测 `grep -rnw 2672` 全仓 0 命中,
    /// 阳性对照 `grep -rnw 7200` 得 7 条,证明探针有效,故那个 0 是阴性证据而非坏探针。
    ///
    /// **为什么用 <see cref="GitIndexRepositoryFiles"/> 而不是目录枚举**:
    /// `ScribeTestMapDeriver.InspectMethod:338` 对**任何** `EnumerateFiles` 调用无条件记
    /// `TestMapUnknownReason.DirectoryEnumeration`,而 `ScribeUnknownDebtPolicy` 对**每个**新增
    /// unknown identity 直接 Block(**不是**撞 280 上限才 Block)。本条的第一版正是这样被
    /// admission 判红的。改用 git index 同时消掉了另一处口径差:`Directory.EnumerateFiles`
    /// 的递归枚举**跟随目录符号链接**,而 `find` 与 git index 都不跟随。
    ///
    /// **红了怎么办**:不要改那个数让它变绿(那由上一条测试拦住),也不要删本测试。
    /// 按 #2535 重新把预算收口到三型之一,或按 #3029 的五条开建条件建拦全量冷建的门,
    /// 然后连同这两条测试一并重写。
    ///
    /// **越线后的后果,如实写**:本测试在必跑的 `make -C tools test` 里,故越线会使**整个仓库的
    /// PR 全部变红**,直到有人收口。这**不是** advisory —— 触发线取 80% 而非 100% 只意味着
    /// 「红出现时预算本身仍够用,收口有时间做」,**不意味着红是软的**。
    /// (此段是对一条评审判词的更正:此前这里写「那条红是提醒,不是事故」,与真实门语义相反。)
    /// </summary>
    [Fact]
    public void ColdBuildBudgetReviewLineHasNotBeenCrossed()
    {
        var leanFiles = GitIndexRepositoryFiles
            .Enumerate(RepositoryLayout.FindRoot())
            .Where(file => file.RelativePath.StartsWith("D5/", StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".lean", StringComparison.Ordinal))
            .ToArray();

        // 放行侧守卫:枚举必须真的选中了内容层。模式拼错(例如 ".leam")会得到空集,
        // 而空集 < 2672 恒成立 —— 那样本测试就永远绿,什么也没守。
        // 下界 2000 取自被审时的实测 2469 之下的一个保守值:它不随日常增长而失真,
        // 又足以把「枚举结果为空/近空」这一整类打错的形态判红。
        Assert.True(
            leanFiles.Length > 2000,
            $"D5 内容层只枚举到 {leanFiles.Length} 个 .lean 文件,远少于预期规模 —— "
            + "这几乎一定是枚举本身坏了(路径前缀、后缀模式或枚举器),而不是仓库真的缩小了。"
            + "在修好它之前,本测试的绿不构成任何证据。");

        Assert.True(
            leanFiles.Length < StrataLint.Cli.LeanCacheBudgetPolicy.ColdBuildBudgetReviewModuleCount,
            $"D5 内容层已有 {leanFiles.Length} 个模块,达到或越过 #3029 裁定的复审触发线 "
            + $"{StrataLint.Cli.LeanCacheBudgetPolicy.ColdBuildBudgetReviewModuleCount}:"
            + "全量冷建的预计耗时已越过 "
            + $"{StrataLint.Cli.LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds}s 预算的 80% 线,"
            + "该 policy-override 的取值依据失效,其「非永久」声明到期。"
            + "按 https://github.com/the-omega-institute/trureturing/issues/2535 重新按三型收口,"
            + "或按 #3029 的五条开建条件建拦全量冷建的门。");
    }
}
