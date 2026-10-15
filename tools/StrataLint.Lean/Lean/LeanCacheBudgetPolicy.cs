using StrataLint.Engine;
namespace StrataLint.EngineeringScope;

internal static class LeanCacheBudgetPolicy
{

    /// <summary>
    /// Default finite per-command cutoff in seconds, not a cold-build completion guarantee.
    ///
    /// **分类:`policy-override`。** 「这不是派生值。」
    /// **域**:LeanCommandBudget for wrapped commands and DependencyFetchBudget for cache get.
    /// Provisioning and each wrapped command have separate bounded attempts; enclosing deadlines
    /// can end them earlier. This is not a total pipeline budget or a cache-closure certificate.
    /// **来源 / 当前选择**:caller-selected minimal infrastructure hotfix under the existing
    /// infrastructure authorization: retain 21600/300, require exact consent for a known
    /// project-zero-olean launch, refuse either unknown probe, and retain automatic incremental
    /// execution for known Project Warm with known Mathlib state. Any-olean warmth does not
    /// certify complete, current dependencies; cold, partial or stale work may exceed the cutoff.
    /// **历史来源**:https://github.com/the-omega-institute/trureturing/issues/2535 and
    /// https://github.com/the-omega-institute/trureturing/issues/4120 record the value's provenance.
    /// The historical 8013-module cost proxy from #3029 is not an active capacity guarantee
    /// or a new threshold. The selected scope does not certify historical full-closure compliance.
    /// **历史正读数**:clonefile ensure 13s, archive-prefix recompilation 78s (19/1513 modules),
    /// warm CI report 766s; these are different operations, not current cold-build benchmarks.
    /// **历史负读数**:1800s against 1656s failed under concurrency; local cold content build
    /// 3388s for 1571 completed modules (28 cores, 2026-08-23, exit 0); ARM Tower 6305s
    /// and an unfinished ARM cold build after 77 minutes (run 32493250519).
    /// The historical 2672-module projection was 5763s, not a fresh measurement.
    /// Checkpoint seed runs 33281766132/33283129303/33286112262 do not supply cold timings.
    /// **新读数**:no current full-cold timing or full-closure benchmark is supplied. Owning tests
    /// exercise refusal, admitted invocation and forwarded bounded budgets, not cold completion.
    /// **owner**:repository τ=0 owner; caller selects this engineering scope, owning guard and
    /// budget tests enforce it. Mathematical checks and explicitly consented producer paths remain.
    /// **退出条件 / 复审触发**:actual wrapped nonzero and timeout exits remain failures; unknown
    /// probes refuse even with consent. Review the selected cutoff with actual workload readings
    /// if it is insufficient, or if deadline, resource, probe or admission semantics change.
    /// **非永久**:a reviewed operational cutoff, not a permanent workload-capacity promise;
    /// module census growth alone neither derives a deadline nor authorizes raising this value.
    /// </summary>
    internal const int DefaultProvisionBudgetSeconds = 21600;

    /// <summary>
    /// 旋钮的下界。低于此值会把正常路径(见上「正读数」)误杀;它只在调用方显式设置
    /// `STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS` 时生效,默认路径不经过它。
    /// 同属上述 `policy-override` 的域,共用同一案号与退出条件。
    /// </summary>
    internal const int MinimumConfigurableBudgetSeconds = 300;

    /// <summary>
    /// Compatibility value for the local archive-fetch cutoff calculation:
    /// 45 minus PostArchiveReserveMinutes gives a 43-minute per-operation bound.
    /// It is independent of ordinary CI's cumulative 30-minute compute allowance
    /// and 360-minute platform job cap (SPEC A22). CI does not fetch Release seeds.
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
