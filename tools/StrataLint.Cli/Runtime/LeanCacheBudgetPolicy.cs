namespace StrataLint.Cli;

internal static class LeanCacheBudgetPolicy
{

    /// <summary>
    /// `LeanCacheProvisioner` 各命令的默认预算,单位秒。
    ///
    /// **分类:`policy-override`。** 「这不是派生值。」
    ///
    /// 三型是**择一**,不是「优先派生、退而求其次」——规矩禁的是「无源未报」(第四形),
    /// 不是「报了 policy-override」。本值走完了另外两型都不可行的论证(见下),
    /// 故落在③,并按该型要求报全七项。
    ///
    /// **日期**:2026-08-25。
    ///
    /// **域**:`LeanCacheProvisioner` 的三个具名消费点 —— `LeanCommandBudget`(承重,
    /// `worktree with-cache-writer` 包裹的任意 Lake 命令)、`DirectoryCopyBudget`
    /// (`cp -R` 回退,实测 0 次发生)、`DependencyFetchBudget`(`lake exe cache get`,
    /// 走到 3 次且差两个数量级)。后两者的继承依据与到期条件写在各自的访问器上。
    ///
    /// **正读数**:正常路径 —— ensure 播种 clonefile **13 秒**;prefix 归档补编
    /// **1m18s**(重编 19/1513 模块);CI 热态报告生产 **12m46s**。
    ///
    /// **负读数**:① 旧值 1800 对当时最贵工作 1656,超配 **1.087**,注释自陈被并发
    /// 「整个吃掉」⟹ 超时失败;② 全量内容层冷建实测 **3388s**(本机 28 核,含并发,
    /// 2026-08-23 `18:56:21→19:52:49`,`EXIT=0`,1571 模块)、**>77 分钟未建完**
    /// (`ubuntu-24.04-arm`,run 32493250519);③ 跨机:`D5/S0/Tower` 一族 81 模块
    /// **6305 秒**@ARM —— 这条同时履行了本文件曾要求的 ANOTHER MACHINE MUST REMEASURE。
    ///
    /// **永久案号**:https://github.com/the-omega-institute/trureturing/issues/2535
    ///
    /// **owner**:仓库 τ=0 owner。
    ///
    /// **退出条件 / 复审触发**:拦住**全量冷建**的 fail-closed 门落地(设计、代价与
    /// 五条开建条件记于 #3029)。届时本值不再需要覆盖冷建,应重新按三型收口。
    /// 在那之前它**必须**覆盖冷建 —— 现有守卫 `AllCold` 是合取,结构上放过
    /// 「mathlib 热 / 内容层冷」这一真实未命中态,故冷建当前无人拦。
    ///
    /// **非永久**:上一条即其非永久性。
    ///
    /// **为何另两型不可行(这是走到③的论证,不是托词)**:
    ///   `capacity-derived` —— 有界工作量是全量冷建成本,而该成本**随仓库增长**
    ///     (D5 六天由 1090 涨到 1711),任何固定上限必失真。**已实证**:PR #3045 以
    ///     `模块数 × 3 × 1.5` 派生,而 clamp 上界对应 1600 模块、落地当天已 1651
    ///     ⟹ 每次求值都被压回上界,即规矩点名的「**常函数掏空分型仍属硬编码**」。
    ///   `relation-derived` —— 不产末值,做不了 timeout。
    ///
    /// **取值 7200 的依据**:须清过负读数②的 3388s 且留出并发余量(负读数①证明
    /// 8% 的余量会被并发吃掉);7200/3388 = **2.13 倍**。它是**选定值,不是算出来的**
    /// —— 这正是本值属③而非①的原因。
    /// </summary>
    internal const int DefaultProvisionBudgetSeconds = 7200;

    /// <summary>
    /// 旋钮的下界。低于此值会把正常路径(见上「正读数」)误杀;它只在调用方显式设置
    /// `STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS` 时生效,默认路径不经过它。
    /// 同属上述 `policy-override` 的域,共用同一案号与退出条件。
    /// </summary>
    internal const int MinimumConfigurableBudgetSeconds = 300;

    /// <summary>
    /// 归档取回所在 job 的预算上限。取自 `.github/workflows/ci.yml` 的 `lean-inspect`
    /// job：`timeout-minutes: 45`。**这是那个值的投影，不是一个独立的选择** ——
    /// `LeanInspectJobBudgetMatchesTheWorkflow` 钉住二者相等，workflow 改了这里就红。
    /// </summary>
    internal const int LeanInspectJobBudgetMinutes = 45;

    /// <summary>
    /// 归档取回**之后**仍必须跑完的工作所占的具名保留：内容层就位后还要生产 canonical
    /// Lean 报告。取自本仓已有的冷跑读数 —— 归档命中时 `lean-reports` 约 18s
    /// （记忆 `lean-cache-worth-190x` 的热态读数），向上取整到分钟并留一倍余量。
    ///
    /// 它**不是**冷编译那一路的预留：那一路根本不该由本预算兜底，冷编译是小时量级
    /// （实测 run 32493250519 内容层编译 >62 min），任何 job 内预算都装不下它，
    /// 故那条路的正解是 #2814 的 fail-closed 门，不是把预算调大。
    /// </summary>
    internal const int PostArchiveReserveMinutes = 2;
}
