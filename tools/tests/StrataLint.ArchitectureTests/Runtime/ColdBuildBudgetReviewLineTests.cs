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
    ///
    /// **它守不住什么(第五轮评审收窄)**:若 Engine 的枚举静默漏掉若干 `.lean`,
    /// 本测试的计数偏小而**假绿** —— 即越线可能发生而它看不见。
    /// 该前提由 issue #3833 追踪。**本测试的声称仅限于「按 Engine 的枚举,计数未越线」**,
    /// 不是「D5 模块数未越线」。
    /// (此段是对一条评审判词的更正:此前这里写「那条红是提醒,不是事故」,与真实门语义相反。)
    /// </summary>
    [Fact]
    public void ColdBuildBudgetReviewLineHasNotBeenCrossed()
    {
        var d5Files = GitIndexRepositoryFiles.EnumerateDeclared(RepositoryLayout.FindRoot(), "D5");
        var leanFiles = d5Files
            .Where(static file => file.RelativePath.EndsWith(".lean", StringComparison.Ordinal))
            .ToArray();

        // 放行侧守卫。此前这里是一条裸下界 `> 2000`,一轮评审判它两条不成立:
        //   ① `2000` 是无来源的瞬时规模数,**对缩仓方向不稳定** ——
        //      本仓实测净减过两次(1487→1486、1115→1114),历史合法树曾为 1486/1114;
        //      而当时的文案把真实缩仓断言成「几乎一定是枚举坏了」,**错误指向修法**;
        //   ② 它只证明「结果大于某数」,不证明**枚举完整** ——
        //      在枚举后插一个 `.Take(2001)` 即可让两条测试都绿而观察者永远看不到越线。
        // 现改为与**同一次枚举的上游集合**做关系断言,不再引入任何裸数:
        //   D5 下的 `.lean` 必须是 D5 tracked 文件的**非空真子集或全集**,
        //   且必须包含 `D5/X_Frontier/Hearts.lean` —— 那是本仓受保护的 sentinel(SL 明文钉住),
        //   它在任何合法树上都存在。截断到任意固定条数都会以极高概率丢掉它,
        //   而把它单独保留下来需要在 diff 里写出这个名字,那正是评审看得见的东西。
        Assert.NotEmpty(d5Files);
        Assert.Contains(
            leanFiles,
            file => file.RelativePath == "D5/X_Frontier/Hearts.lean");
        Assert.True(
            leanFiles.Length <= d5Files.Count,
            "`.lean` 集合不可能大于它所属的 D5 tracked 集合 —— 枚举自相矛盾。");

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

    /// <summary>
    /// **可达性契约**:一次只改 D5 的变更**必须**选中上面那个观察者。
    ///
    /// 这条是一轮评审用实测买来的。上一版为了避开 unknown 棘轮改用
    /// `GitIndexRepositoryFiles.Enumerate`(deriver 不识别的名字)—— 那确实消掉了 unknown,
    /// **但同时消掉了 `D5` 输入归因**:评审席在临时克隆里只新增一条 D5 `.lean`,
    /// 跑 canonical planner 得到 `kind=selected, selected_count=185, cold_build_observer=[]`。
    /// 即**观察者对它唯一要观察的那类变更是盲的**;而 D5 模块数的增长几乎全部来自 D5-only PR,
    /// 故它当时几乎不可能red——一个永远不会红的观察者不是观察者。
    ///
    /// 现在观察者走 `EnumerateDeclared(root, "D5")`,deriver 把 `"D5"` 记为 declared input,
    /// `EngineeringTestPlanDeriver` 的 `Covers` 是前缀匹配,故任何 `D5/**` 变更都会选中它。
    /// **本测试就是那条链的机器保证** —— 没有它,下一次有人换掉枚举方式时,
    /// 观察者会再次静默失去可达性而两条断言依旧全绿。
    /// </summary>
    [Fact]
    public void ColdBuildBudgetReviewLineObserverIsSelectedByD5OnlyChanges()
    {
        var plan = EngineeringTestPlanDeriver.DeriveRepository(
            RepositoryLayout.FindRoot(),
            ["D5/S3/Constants/Irrationality/SyntheticColdBuildProbe.lean"]);

        Assert.Contains(
            plan.Tests,
            test => test.Id.Contains(
                nameof(ColdBuildBudgetReviewLineHasNotBeenCrossed),
                StringComparison.Ordinal));
    }

    /// <summary>
    /// **`EnumerateDeclared` 自己的钉子** —— 它必须返回该前缀下的**每一个** tracked 文件。
    ///
    /// 这条是第四轮评审用实测买来的。此前 `ColdBuildBudgetReviewLineHasNotBeenCrossed`
    /// 想靠「与同一次枚举的上游集合做关系断言 + 一个 sentinel」自证枚举完整,
    /// 评审席实测证伪:子集断言 `leanFiles.Length &lt;= d5Files.Count` **由构造恒真**
    /// (`leanFiles` 就是从 `d5Files` 过滤来的),而单个 sentinel **可以被保留后任意截断** ——
    /// 它在 `EnumerateDeclared` 里加 `OrderByDescending(...).Take(n)` 并保留 `Hearts.lean`,
    /// 那一条与另外三条断言**全部照绿**,观察者从此永远看不到越线。
    ///
    /// **修法不是给消费者加更多断言,是给这个包装它自己的红。**
    /// 本测试独立跑一次全量 <see cref="GitIndexRepositoryFiles.Enumerate"/> 并自行过滤,
    /// 与 <see cref="GitIndexRepositoryFiles.EnumerateDeclared"/> 的结果**逐项比对**;
    /// 任何截断、重排丢项或前缀语义漂移都会在这里红。
    ///
    /// **保证边界(第五轮评审实测收窄,原文写错了)**:本测试**不证明**
    /// `StrataLint.Engine.GitIndexRepositoryFiles.Enumerate` 自身完整。
    ///
    /// 此处原本写的是「那是它的义务,由它众多的消费者共同承担(变异它会红一大片)」。
    /// **那句话被实测证伪**:评审席在 Engine 的 `File.Exists` 过滤后省略**一个**文件
    /// (`D5/S0/Asymptotics/Bonferroni/TailBounds.lean`),`exit=0`、232/232 全过、
    /// **红消费者 0 个**。只有**粗**截断(降序 `Take(32776)`)才会红 14 个,
    /// 而那 14 条守的是别的不变量,只是碰巧连带失败。
    ///
    /// 故准确的表述是:**Engine 的枚举在单文件粒度上无任何钉子**,已立 issue #3833。
    /// 本测试证明的是**这个包装没有在 Engine 之上再丢东西**——仅此而已。
    /// 它与它的消费者 `ColdBuildBudgetReviewLineHasNotBeenCrossed` 一样,
    /// **都以「Engine 枚举完整」为未经证明的前提**;那个前提由 #3833 追踪,不在本文件内解决。
    ///
    /// **为什么不在这里解决**:任何住在 `tools/tests/**` 的独立比对若也调 `Enumerate`,
    /// 就与被测对象同源;改用目录遍历则撞 `TestMapUnknownReason.DirectoryEnumeration`
    /// 的 unknown 棘轮(对每个新增 unknown identity 直接 Block)。
    /// 需要的是给 Engine 自己一个钉子,而不是让它的某个消费者去证明它。
    ///
    /// **为什么单独一条测试而不并进上面那条**:本测试调无前缀的 `Enumerate`,
    /// deriver 因此把它归因为**整仓**;而上面那条必须保持 `D5` 归因,
    /// 否则它对 D5-only 变更的可达性就没了(那是第二轮评审实测过的缺口)。
    /// 两条各自归因,互不污染。
    /// </summary>
    [Fact]
    public void EnumerateDeclaredReturnsEveryTrackedFileUnderThePrefix()
    {
        var root = RepositoryLayout.FindRoot();

        var independent = GitIndexRepositoryFiles.Enumerate(root)
            .Where(static file => file.RelativePath.StartsWith("D5/", StringComparison.Ordinal))
            .Select(static file => file.RelativePath)
            .ToArray();
        var declared = GitIndexRepositoryFiles.EnumerateDeclared(root, "D5")
            .Select(static file => file.RelativePath)
            .ToArray();

        Assert.NotEmpty(independent);
        Assert.Equal(independent, declared);
    }
}
