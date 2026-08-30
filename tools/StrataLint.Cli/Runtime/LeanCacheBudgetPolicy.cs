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
    /// **日期**:2026-08-30(第二次收口;首次收口 2026-08-25 取值 7200,案号 #2535)。
    ///
    /// **修订记录(2026-08-30)**:复审触发线 ②(当时 2672 模块)被跨过 —— dev `9b629c376` 实测
    /// `find D5 -name '*.lean' | wc -l` = 2672,观察者 `ColdBuildBudgetReviewLineHasNotBeenCrossed`
    /// 如其设计变红——它在必跑的架构测试里,故 dev 自身到线后**所有** PR(含只改一行文档的、
    /// 含干净的 dev 树本身)一律红,不只是触碰 D5 的(https://github.com/the-omega-institute/trureturing/issues/4120)。
    /// 本次是对该到期的**重新收口**,不是「改大让它绿」:型别不变、论证重走、读数更新、复审线重算。
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
    /// **6305 秒**@ARM —— 这条同时履行了本文件曾要求的 ANOTHER MACHINE MUST REMEASURE;
    /// ④(2026-08-30 新增)锚点投影:2.156588 s/模块(= 3388/1571;1571 是那次冷建**建成**的模块数,
    /// 当时 census 为 1575 个 `.lean`,取建成数为分母使 s/模块偏大,是保守方向)× 2672 =
    /// 5762.40,**ceil 为 5763s**,即 7200 的 80.0%,首次收口的取值依据按其自设判据到期;
    /// ⑤(2026-08-30 新增;第二、三轮评审两次勘正 run 链与树的归属)CI 侧观测(`lean-cache-seed-manual.yml`,
    /// v4.33 集成分支,ubuntu-24.04-arm,12 分钟检查点 × 6/轮,跨轮以进度快照续建)。三轮 run 的
    /// `workflow_dispatch` 挂在不同 dev 提交上,但 checkout 日志亲验三轮都检出**同一棵**集成候选树
    /// `ab396a337a16aedc5a7c9cf0d7c1bc1becc8a4d8`(2649 个 D5 `.lean`;三份日志各命中该 SHA 一次):
    /// run 33281766132(restore 1s 无命中 = cache-miss 起点;checkpoint 1 于 12 分钟处失败但存下 97 MB
    /// 快照)→ run 33283129303(恢复 97 MB,建造 72 分钟未完成,存 1.18 GB)→ run 33286112262(恢复
    /// 1.18 GB,再建 72 分钟仍未报完成)。**固定树、检查点续建**:在「快照恢复不丢失已建产物」的假设下,
    /// 该树在 ARM 上的冷建 **≥ 8640s**(第二、三轮之和;若首轮 12 分钟的产物计入则 ≥ 9360s)且仍未完成。
    /// 且 `lean-inspect` job 自身 `timeout-minutes: 45`,故本预算在 CI 上从不承重,
    /// 只约束本机 `with-cache-writer` 包裹的 Lake 命令。
    /// ⑥(2026-08-30,#4122 architecture/quality 席三轮)**嵌套 deadline 取最小**:本机 `make lean-report`
    /// 的 worker `tools/lean-inspector/inspect.sh`(role=lean-producer)最坏顺序跑
    /// <see cref="InspectorSequentialLakePhasesWorstCase"/> = 3 条 Lake 阶段,每条之前有 ensure 前导
    /// (最多 <see cref="ArchiveFetchBudgetSeconds"/>),阶段之间有非 Lake 工作
    /// (<see cref="SupervisorNonLakeReserveSeconds"/>);外层是 `report-supervisor.sh` 的 `BUILD_TIMEOUT_SECONDS`
    /// (#403),有效上限 = min(本值, 外层 − 已耗)。外层留在 7200、与本值「相等」、或只取 3 × 本值,
    /// 都使后面的阶段只剩余量。故 lean-producer 的外层 = <see cref="InspectorSupervisorBudgetSeconds"/>
    /// = 3 × (21600 + 2580) + 3600 = 76140,由 `LeanProducerHoldBudgetEqualsTheInspectorComposite` 钉住相等;
    /// 消费者角色保留 7200(`ConsumerHangBoundIsUnchangedByTheProducerComposite`)。
    ///
    /// **永久案号**:https://github.com/the-omega-institute/trureturing/issues/2535(首次收口)
    ///   → https://github.com/the-omega-institute/trureturing/issues/4120(2026-08-30 修订)
    ///
    /// **owner**:仓库 τ=0 owner。
    ///
    /// **退出条件 / 复审触发**(两条,任一为真即须重新收口):
    ///   ① 拦住**全量冷建**的 fail-closed 门落地(设计、代价与五条开建条件记于 #3029)。
    ///      届时本值不再需要覆盖冷建。在那之前它**必须**覆盖冷建 —— 现有守卫 `AllCold`
    ///      是合取,结构上放过「mathlib 热 / 内容层冷」这一真实未命中态,故冷建当前无人拦。
    ///      **① 是一个动作,不可机器判**,故它不能单独承担「非永久」。〔2026-08-30 勘注:生产者侧
    ///      的种子 workflow `.github/workflows/lean-cache-seed-manual.yml` 已实际存在并跑过
    ///      (负读数⑤),#3029 「新 config 的首个 PR 结构上必无种子」这一前提因此改变;
    ///      门的**消费侧**仍未建,由 #4120 的后续单承接,本次不建(16′ 剥洋葱)。〕
    ///   ② D5 内容层模块数达到 <see cref="ColdBuildBudgetReviewModuleCount"/>(2026-08-30 重算)。
    ///      **② 可机器判且有观察者**(见该常数的声明),这是「非永久」的实际兑现处。
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
    /// **取值 21600 的依据**:选定规则与首次相同 —— 须清过**当前规模**的冷建读数且留出并发余量
    /// (负读数①证明 8% 的余量会被并发吃掉;首次取 7200/3388 = 2.13 倍为足)。当前规模的冷建读数
    /// 取负读数④(本机投影 5763s,上界侧)与⑤(CI 固定树下界 ≥ 8640s,ARM)中的较大者 8640s;
    /// 21600/8640 = **2.5 倍**(对本机投影为 3.75 倍),取整小时使它一望可知是选定值。
    /// **不取更小**:对 ⑤ 的 2 倍(17280)已贴近,对 ④ 的 2 倍(11526)只在今日规模上成立,
    /// 而本值的域是本机 Lake 命令的挂死上限,误杀一次合法冷建的代价(半建的 `.lake` 无 stamp,
    /// 连带作废 donor 资格,#2762)高于多等一会儿;**不取更大**:预算必须封顶,否则挂死检测失效。
    /// 它是**选定值,不是算出来的** —— 这正是本值属③而非①的原因。
    /// </summary>
    internal const int DefaultProvisionBudgetSeconds = 21600;

    /// <summary>
    /// 上述 `policy-override` 的**复审触发线**:D5 内容层模块数达到此值时,它的取值依据失效。
    ///
    /// **来源(2026-08-30,#4120 修订)**:首值 2672 由 #3029 裁定(锚点 = 负读数②的
    /// 3388s / 1571 模块 = 2.156588 s/模块,7200 的 80% 线)。本次重算把取整规则写明:
    /// **`ceil(0.8 × DefaultProvisionBudgetSeconds / 2.156588)` = ceil(8012.66) = 8013,单阶段向上取整**。
    /// 锚点沿用 #3029 的本机上界侧读数,**未重测**:重测需要一次全量冷建,而那正是本值要避免的事;
    /// 负读数⑤ 的 CI 固定树下界(≥ 8640s @ 2649 模块,ARM)高于本机投影,说明本机锚点对 CI 不是上界——
    /// 但本值的域是本机(见 域 与 负读数⑤),复审线按本机锚点算。lean-producer 的外层 supervisor
    /// 预算为本值的复合(负读数⑥)且由测试钉住,故本线对真正杀进程的那层不迟到。本文件登记它,
    /// 由 `ColdBuildBudgetReviewLineTests.ColdBuildBudgetReviewLineHasNotBeenCrossed` 盯住。
    ///
    /// **为什么需要这一条**:2026-08-26 实测 `grep -rnw 2672` 全仓 **0 命中**
    /// (阳性对照 `grep -rnw 7200` 得 7 条,证明探针有效)—— 即这条退出条件当时
    /// **没有任何机器在看**。上面的 **非永久** 声明,在有观察者之前是无法兑现的。
    ///
    /// 按第 20 条这属**检测层**(便宜,不是预防);按「引用必须机械可判,悬空即红」,
    /// 一个无 fail-closed 消费者的退出条件与悬空引用同形:指错了没人读,永远不会红。
    ///
    /// **实际增长(读数,不是推理)**:2026-08-26 `a9b3cb7b9` 为 2033;两日后 `3add627e3` 为 2469。
    /// 〔勘正:此前这里写「该量单调不减(冻结律),故必然为真」。**那是假的** ——
    /// 一条评审判词实测出模块数**净减过**至少两次(`a6ff2c349` 1487→1486、`3b0c812ef` 1115→1114);
    /// 且即便单调不减也不逻辑蕴含跨越固定线(常数序列即反例)。故本条**不再声称必然性**,
    /// 只声称:该量在实测区间内快速增长,而它到达时无人观察 —— 后者才是本观察者存在的理由。〕
    ///
    /// **越线后的后果,如实写**:观察者在必跑测试里,故越线会使**整个仓库的 PR 全部变红**,
    /// 直到有人收口。80% 而非 100% 只意味着「红出现时预算本身仍够用,收口有时间做」,
    /// **不意味着红是软的**。〔勘正:此前这里写「那条红是提醒,不是事故」,与真实门语义相反。〕
    ///
    /// **首值的取整缺口(已闭合)**:本文件曾记 `7200 × 0.8 / 2.156588 = 2670.885`,而 2672 只能由
    /// 未声明的两阶段取整复现。本次修订以上面写明的单阶段规则重算,该缺口不再存在。
    ///
    /// **越线时实际发生了什么(2026-08-30 读数)**:2026-08-26 `a9b3cb7b9` 2033 → 08-28 `3add627e3` 2469
    /// → 08-30 `9b629c376` 2672,四天跨过 80% 线而无人在此期间收口;观察者如设计地红了。
    /// </summary>
    internal const int ColdBuildBudgetReviewModuleCount = 8013;

    /// <summary>
    /// `tools/lean-inspector/inspect.sh` 最坏情况下**顺序**执行的、各自受
    /// <see cref="DefaultProvisionBudgetSeconds"/> 约束的 Lake 阶段数:`lake build`(:130)+
    /// delta 子集 inspect + 全量回退 inspect(`invoke_inspector` 的两个调用点 :306/:326)= **3**。
    /// 不是选定值,是脚本结构的计数,由 `InspectorSequentialLakePhaseCountMatchesTheScript` 从脚本文本
    /// 重数并钉住;脚本多一条 Lake 阶段即红。它的唯一消费者是嵌套 deadline 关系:supervisor 的外层
    /// `BUILD_TIMEOUT` 必须 ≥ 本数 × 内层预算(`HolderBudgetCoversTheInspectorsSequentialLakePhases`)。
    /// </summary>
    internal const int InspectorSequentialLakePhasesWorstCase = 3;

    /// <summary>
    /// 每条 Lake 阶段之前的 ensure 前导在 project-cold 路径上最多花在归档取回上的时间:
    /// `LeanCacheEnsureCommand:671-674` 用的同一式 `(LeanInspectJobBudgetMinutes − PostArchiveReserveMinutes) × 60`
    /// = 2580s;超时被捕获并降级为源编译(`LeanCacheEnsureCommand:287`),故它是加在 Lake 预算之前的一段,
    /// 不与之重叠。**投影,不是独立选择**。
    /// </summary>
    internal const int ArchiveFetchBudgetSeconds =
        (LeanInspectJobBudgetMinutes - PostArchiveReserveMinutes) * 60;

    /// <summary>
    /// lean-producer 外层预算中 Lake 阶段**之外**的工作的具名保留:模块枚举、delta 规划、材料压缩
    /// (`materials.py compact`)、合并与序列化、进程启动。
    ///
    /// **分类:`policy-override`。** 「这不是派生值。」**日期**:2026-08-30。**域**:仅 `report-supervisor.sh`
    /// 对 role=lean-producer 的复合外层预算(`InspectorSupervisorBudgetSeconds` 的加项),不作用于任何
    /// Lake 命令。**正读数**:CI 热态整份 lean-report 生产 12m46s = 766s(2026-08-25,含 Lake no-op build
    /// 与 inspect,非 Lake 部分是其真子集)。**负读数**:无——非 Lake 部分从未被单独计时,记 `open`。
    /// **取值 3600 的依据**:≥ 4.7 × 766s,取整小时;选定值。**永久案号**:同主声明的链
    /// #2535 → #4120(#4122 第三轮 architecture/quality 席:复合预算须含非 Lake 保留)。**owner**:仓库 τ=0 owner。
    /// **退出条件 / 复审触发**:与主声明相同(门①落地,或复审线②);另加:非 Lake 部分一旦被单独计时,
    /// 本值须按该读数重新收口。**非永久**:上一条即其非永久性。
    /// </summary>
    internal const int SupervisorNonLakeReserveSeconds = 3600;

    /// <summary>
    /// role=lean-producer 的 supervisor 外层预算 = 阶段数 × (前导 + Lake) + 非 Lake 保留
    /// = 3 × (21600 + 2580) + 3600 = **76140**。派生自本文件的四个已分类量,不是新的选定值;
    /// `report-supervisor.sh` 的 `LEAN_PRODUCER_BUILD_TIMEOUT_SECONDS` 字面量由
    /// `LeanProducerHoldBudgetEqualsTheInspectorComposite` 钉住相等。消费者角色不用它(它们不跑 Lake,
    /// #403 的 7200 原样保留,由 `ConsumerHangBoundIsUnchangedByTheProducerComposite` 钉住)。
    /// </summary>
    internal const int InspectorSupervisorBudgetSeconds =
        InspectorSequentialLakePhasesWorstCase * (DefaultProvisionBudgetSeconds + ArchiveFetchBudgetSeconds)
        + SupervisorNonLakeReserveSeconds;

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
