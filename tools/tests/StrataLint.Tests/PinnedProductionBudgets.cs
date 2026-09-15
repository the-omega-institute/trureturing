using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// 以**直接引用生产声明**的方式钉住的预算(pinned-production-constant,第Ⅵ节「量腹而食」)。
/// 需要 Engine / Cli 的 internal 可见性,而那份授权只给了本程序集,故不迁往 TestSupport。
///
/// 注:BoundedProcessRunnerBudget 实测**零消费者**(唯一同名命中是类名
/// BoundedProcessRunnerBudgetTests,是名字撞车不是使用)。本层不删 —— 那是另一件事,
/// 混进来会让这一层同时做两件事(第 16′ 条)。
/// </summary>
public static class PinnedProductionBudgets
{

    public static readonly TimeSpan BoundedProcessRunnerBudget = BoundedProcessRunner.HangDetectionBudget; // pinned-production-constant: direct production declaration
    public static readonly TimeSpan LeanCacheProvisionBudget = TimeSpan.FromSeconds(LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds); // pinned-production-constant: LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds
    public static readonly TimeSpan LeanCacheProvisionCeiling = TimeSpan.FromSeconds(LeanCacheProvisioner.MaxProvisionBudgetSeconds); // pinned-production-constant: direct production declaration
    public static readonly TimeSpan LeanCacheRetryOne = LeanCacheProvisioner.CloneRetryBackoffs[0]; // pinned-production-constant: direct production declaration
    public static readonly TimeSpan LeanCacheRetryTwo = LeanCacheProvisioner.CloneRetryBackoffs[1]; // pinned-production-constant: direct production declaration
    public static readonly TimeSpan LeanCacheRetryThree = LeanCacheProvisioner.CloneRetryBackoffs[2]; // pinned-production-constant: direct production declaration
    public static readonly TimeSpan LeanCacheRetryFour = LeanCacheProvisioner.CloneRetryBackoffs[3]; // pinned-production-constant: direct production declaration
}
