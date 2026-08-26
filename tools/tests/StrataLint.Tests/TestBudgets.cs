using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public static class TestBudgets
{
    public static readonly TimeSpan LocalProcessHangGuard = TimeSpan.FromSeconds(2); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan ShortProcessHangGuard = TimeSpan.FromSeconds(5); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan ScriptProcessHangGuard = TimeSpan.FromSeconds(10); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan PlaybookProcessHangGuard = TimeSpan.FromSeconds(15); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan WorkflowProcessHangGuard = TimeSpan.FromSeconds(60); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan LeanProcessHangGuard = TimeSpan.FromSeconds(120); // infrastructure-hang-guard: never bears a test verdict
    public static readonly TimeSpan ReportSupervisorHangGuard = TimeSpan.FromMinutes(5); // infrastructure-hang-guard: never bears a test verdict

    public static readonly TimeSpan BoundedProcessRunnerBudget = TimeSpan.FromMinutes(5); // pinned-production-constant: BoundedProcessRunner.HangDetectionBudget
    public static readonly TimeSpan LeanCacheProvisionBudget = TimeSpan.FromSeconds(LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds); // pinned-production-constant: LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds
    public static readonly TimeSpan LeanCacheProvisionCeiling = TimeSpan.FromSeconds(7200); // pinned-production-constant: LeanCacheBudgetPolicy maximum
    public static readonly TimeSpan LeanCacheRetryOne = TimeSpan.FromMilliseconds(250); // pinned-production-constant: LeanCacheProvisioner retry schedule
    public static readonly TimeSpan LeanCacheRetryTwo = TimeSpan.FromMilliseconds(500); // pinned-production-constant: LeanCacheProvisioner retry schedule
    public static readonly TimeSpan LeanCacheRetryThree = TimeSpan.FromMilliseconds(1000); // pinned-production-constant: LeanCacheProvisioner retry schedule
    public static readonly TimeSpan LeanCacheRetryFour = TimeSpan.FromMilliseconds(2000); // pinned-production-constant: LeanCacheProvisioner retry schedule
}
