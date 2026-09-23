namespace StrataLint.TestSupport;

/// <summary>
/// 三个测试程序集共用的时长常量。**此处只放不依赖生产声明的值**。
///
/// 依赖生产内部声明的那七个(pinned-production-constant)留在 StrataLint.Tests 的
/// PinnedProductionBudgets:Engine / Cli 的 InternalsVisibleTo 只授权给了那一个程序集,
/// 把它们一并搬来会迫使生产程序集向本项目额外开放 internal —— 那是**没有消费者要求的**放宽。
///
/// 实测依据(dev ae7d5b8591):ScriptTests 只用 ScriptProcessHangGuard(16 处);
/// ArchitectureTests 只用 ScriptProcessHangGuard(3)与 ZeroDuration(2);
/// LeanCache* 与 BoundedProcessRunnerBudget 的消费者全在 StrataLint.Tests 内。
/// </summary>
public static class TestBudgets
{
    public static readonly TimeSpan ZeroDuration = TimeSpan.Zero; // pinned-production-constant: System.TimeSpan.Zero
    public static readonly TimeSpan LocalProcessHangGuard = TimeSpan.FromSeconds(2); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan ShortProcessHangGuard = TimeSpan.FromSeconds(5); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan ScriptProcessHangGuard = TimeSpan.FromSeconds(10); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan PlaybookProcessHangGuard = TimeSpan.FromSeconds(15); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan WorkflowProcessHangGuard = TimeSpan.FromSeconds(60); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan LeanProcessHangGuard = TimeSpan.FromSeconds(120); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan LongWorkflowProcessHangGuard = TimeSpan.FromMinutes(3); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan ReportSupervisorHangGuard = TimeSpan.FromMinutes(5); // infrastructure-hang-guard: never bears a test verdict
}
