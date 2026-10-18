using System.Text;

namespace StrataLint.ReportSupervisor.Tests;

public sealed class RunnerDiagnosticsTests
{
    [Theory]
    [InlineData("test_disabled_exec_preserves_pid_argv_and_exit")]
    [InlineData("test_true_enables_observation_and_preserves_business_exit")]
    [InlineData("test_nonlinux_is_explicit_and_transparent")]
    [InlineData("test_observer_failure_preserves_exit_and_redacts_error")]
    [InlineData("test_missing_tool_permissions_and_early_observer_exit_fail_open")]
    [InlineData("test_memory_uses_cgroup_current_limit_and_oom_events")]
    [InlineData("test_dispatch_adds_diagnostics_only_for_literal_true")]
    [InlineData("test_cleanup_failure_is_redacted_and_keeps_business_exit")]
    [InlineData("test_stale_process_or_group_identity_cannot_receive_cleanup")]
    [InlineData("test_partial_tracer_start_failure_still_reaps_real_process")]
    [InlineData("test_console_failure_and_partial_writes_preserve_exit")]
    [InlineData("test_linux_signal_sender_and_term_join_entire_business_tree")]
    [InlineData("test_linux_sudo_observer_detaches_without_signalling_worker")]
    public void OptInObservationPreservesBusinessAndReapsObservers(string test)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.ReportSupervisor.Tests/Fixtures/runner_diagnostics_contract.py"),
                "RunnerDiagnosticsTests." + test],
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
