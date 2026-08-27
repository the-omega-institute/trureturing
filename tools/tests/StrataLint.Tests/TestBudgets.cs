using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

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

    public static readonly TimeSpan BoundedProcessRunnerBudget = BoundedProcessRunner.HangDetectionBudget; // pinned-production-constant: direct production declaration
    public static readonly TimeSpan LeanCacheProvisionBudget = TimeSpan.FromSeconds(LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds); // pinned-production-constant: LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds
    public static readonly TimeSpan LeanCacheProvisionCeiling = TimeSpan.FromSeconds(LeanCacheProvisioner.MaxProvisionBudgetSeconds); // pinned-production-constant: direct production declaration
    public static readonly TimeSpan LeanCacheRetryOne = LeanCacheProvisioner.CloneRetryBackoffs[0]; // pinned-production-constant: direct production declaration
    public static readonly TimeSpan LeanCacheRetryTwo = LeanCacheProvisioner.CloneRetryBackoffs[1]; // pinned-production-constant: direct production declaration
    public static readonly TimeSpan LeanCacheRetryThree = LeanCacheProvisioner.CloneRetryBackoffs[2]; // pinned-production-constant: direct production declaration
    public static readonly TimeSpan LeanCacheRetryFour = LeanCacheProvisioner.CloneRetryBackoffs[3]; // pinned-production-constant: direct production declaration
}
