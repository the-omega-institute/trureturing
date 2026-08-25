namespace StrataLint.Cli;

internal static class LeanCacheBudgetPolicy
{
    /// policy-override (CLAUDE.md 第Ⅵ节「量腹而食」第三型) — 2026-08-20.
    ///
    /// THIS IS NOT A DERIVED VALUE. It is a declared override, not `capacity-derived`
    /// and not `relation-derived`; it is not a function of vCPU, memory, or any other
    /// machine capacity, and it must not be presented as one.
    ///
    /// Domain — NARROWED 2026-08-24 (#2535). This value is now sized for exactly one
    /// consumer and inherited by the others through named accessors that each carry their
    /// own justification, so the sharing is explicit rather than incidental:
    ///   LeanCacheProvisioner.LeanCommandBudget   — load-bearing. The one arbitrary command
    ///       `LeanCacheEnsureCommand` runs for `worktree with-cache-writer`: `lake build`
    ///       from the Makefile, and both the `lake build` and the
    ///       `lake env lean --run Inspector.lean` that `tools/lean-inspector/inspect.sh`
    ///       passes. THIS is what the number is chosen against.
    ///   LeanCacheProvisioner.DirectoryCopyBudget — the `cp -R` donor clone fallback.
    ///       Measured 0 occurrences (47 ensure receipts, `clonefile_errno` all null).
    ///   LeanCacheProvisioner.DependencyFetchBudget — `lake exe cache get`. Reached 3 times,
    ///       two orders of magnitude below this ceiling (ensure end-to-end 13 seconds).
    /// The previous text accepted "a hung `cp` is tolerated for the build's budget" as the
    /// cost of triage. That cost is not removed by the rename — the values are still equal —
    /// but it is no longer silent: each inheritance states the measurement that justifies it
    /// and the condition under which it expires. Deriving separate literals for a
    /// zero-occurrence path would turn one unsourced constant into three, which is the rule's
    /// fourth form multiplied, not a fix (CLAUDE.md 20-double-prime). Deliberately no line numbers: an earlier version of this
    /// comment carried five line references, and the three that pointed into this file
    /// were copied from the pre-insertion text. Inserting the comment moved each of those
    /// three targets down twelve lines, so all three were false the moment they were
    /// committed. (The two cross-file references were still correct; the point is that a
    /// local anchor cannot survive its own comment.)
    /// Out of domain: the `dotnet restore` timeout in `WorktreeCommand`, a separate knob
    /// that merely happened to carry the same literal and is not touched here.
    ///
    /// Positive readings — ElonSG only, 2026-08-20; ANOTHER MACHINE MUST REMEASURE, and
    /// none of these numbers is reproducible from this repository, so they are this
    /// author's reported measurements rather than committed evidence. Building the
    /// single most expensive subgraph — `S0/Tower/TribonacciPeriodicElevenDistinct/
    /// {PartB..PartF}` with `S0/Tower/NodupAssembly/PeriodEleven` — took 1656s on the
    /// main checkout and 1212s on a lane, both `LAKE_RC=0`. Those modules landed
    /// 2026-08-18, so this ceiling first became reachable two days before this override.
    ///
    /// Negative readings — same machine, same day, same caveat. `make lean-report`
    /// returned `EXIT=2` with `lake timed out after 1800 seconds` twice in a row. The
    /// second failure needed only three remaining modules, which is the load-bearing
    /// observation: the wall is struck by individual expensive subgraphs, not by module
    /// count. The slack left under the old ceiling was (1800 - 1656) / 1800 = 8%, and
    /// concurrent load from other drivers on this machine was observed holding CPU idle
    /// at 0% for over 25 minutes, which consumes that slack outright.
    ///
    /// Slack — REMEASURED 2026-08-23, and it is now WORSE than the ceiling this value
    /// replaced. The negative reading below rejected 1800 because its slack over the then
    /// most-expensive work was (1800-1656)/1800 = 8%, "consumed outright" by concurrent load.
    /// A full content-layer cold build now measures 3388s on this machine (56m28s, EXIT=0,
    /// 1571 modules, 2026-08-23) — and that sample was itself taken with two other sessions'
    /// codex seats running, so the concurrency the old note blamed is already inside it.
    /// Slack today: (3600-3388)/3600 = 5.9%, BELOW the 8% that failed. Cross-machine:
    /// `S0/Tower` alone costs 6305s across 81 modules on ubuntu-24.04-arm (run 32493250519),
    /// which discharges this comment's own ANOTHER MACHINE MUST REMEASURE for the family.
    /// The work term is also still growing: D5 held 773 `.lean` files on 2026-08-15 and 1575
    /// on 2026-08-24. Raising the literal a third time (1800 -> 3600 -> ?) would replay the
    /// same defect with a new number and is deliberately NOT done here; the exit condition
    /// below is the fix.
    ///
    /// Value: 3600s is a chosen round hour, NOT a derivation. It has to clear the
    /// measured 1656s with room for the contention above, and it is half the ceiling
    /// this knob's existing escape hatch already sanctions (`Math.Clamp(..., 300, 7200)`
    /// below), so it widens no bound that was not already permitted. Any ratio one can
    /// compute against 1656 is arithmetic after the fact, not a rule that produced this
    /// number; do not read one into it.
    ///
    /// Case: https://github.com/the-omega-institute/trureturing/issues/2535
    /// Owner: repository owner (directed 2026-08-20 as triage while the durable cache
    /// fix proceeds separately on macstudio-4).
    /// NOT PERMANENT.
    ///
    /// Exit condition, branch one — DISCHARGED 2026-08-23. It read: "retire this
    /// override once the machine-level D5 build cache lands, because a lane that clones
    /// a complete cache never pays this build at all". The cache landed (#2729, #2762
    /// closed; nine content-layer archives published; two automatic archive entries in
    /// LeanCacheEnsureCommand; the clonefile donor path). Receipt, taken on a lane whose
    /// `.lake` did not exist at all:
    ///   LEAN_CACHE {"status":"seeded","method":"clonefile","clonefile_attempts":1,
    ///               "mathlib_olean_state":"warm","project_olean_state":"warm",
    ///               "archive_status":"not_attempted"}
    ///   13 seconds wall clock; 1430 content-layer and 8550 dependency-layer oleans.
    /// Three concurrent blind codex-cli seats (exit-condition literalism, derivability,
    /// cadence) read this branch as satisfied, unanimously.
    ///
    /// Exit condition, branch two — STRUCTURALLY UNAVAILABLE, not merely unmet. It asked
    /// for "a genuine derivation whose independent variable includes the cost of the most
    /// expensive single subgraph, not machine capacity alone". Under the repository's
    /// capacity-derivation rule a `capacity-derived` value is `C_i = min_j U_{i,j} - R_i`
    /// with `q_i = floor(C_i / r_i)`; every independent variable there is a capacity or a
    /// single-task resource, so the most-expensive-subgraph term has nowhere to live, and
    /// `relation-derived` yields no terminal value at all. The derivability seat reached
    /// this independently. Do not wait on this branch; it cannot be walked while one value
    /// spans `cp`, `cache-get`, `cache-clean` and every Lake command.
    ///
    /// Exit condition, REPLACED — this is what the case now tracks. Split this single
    /// wide-domain value into per-command budgets owned by the commands themselves, then
    /// classify each under exactly one of the three types. Retiring the override by
    /// deleting the constant is explicitly NOT the discharge: a bare 3600 with no type is
    /// the fourth form the rule forbids, which is strictly worse than a cased override.
    /// The value must still clear the measured 1656s of the single most expensive
    /// subgraph, which is why it remains in the capacity domain and cannot be reclassified
    /// as an out-of-domain liveness ceiling.
    ///
    /// Also still open and unchanged by the cache work: the positive and negative readings
    /// below are ElonSG-only and ANOTHER MACHINE MUST REMEASURE.
    ///
    /// SUPERSEDED 2026-08-24 (#2535). Kept only as the historical literal the derivation
    /// below replaced, so that the readings above stay attached to the number they
    /// justified. Nothing consumes it.
    internal const int SupersededPolicyOverrideSeconds = 3600;

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
