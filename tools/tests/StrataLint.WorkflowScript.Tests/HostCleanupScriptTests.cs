using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.WorkflowScript.Tests;

public sealed class HostCleanupScriptTests
{
    [Theory]
    [InlineData("native_bytes_and_stdin")]
    [InlineData("direct_owner_pid_handled_and_unhandled_int_term")]
    [InlineData("group_signal_has_one_native_delivery")]
    [InlineData("shared_common_directory_and_correlation")]
    [InlineData("failing_destination_is_best_effort")]
    [InlineData("bash_owner_boundary")]
    [InlineData("bash_group_signal_matches_native")]
    [InlineData("concurrent_rows_and_inherited_descriptor")]
    [InlineData("elapsed_and_deleted_source_completion")]
    [InlineData("csharp_completion_after_cwd_deletion")]
    [InlineData("python_owner_children_have_immediate_parent")]
    [InlineData("warm_donor_sigpipe_has_native_stderr")]
    public void MaintenanceLoggingPreservesCommandBehavior(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorkflowScript.Tests/Fixtures/maintenance_log_tests.py"),
                root, "MaintenanceLogTests.test_" + probe], root, TimeSpan.FromSeconds(90), 1024 * 1024,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains("Ran 1 test", Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("runlocal_stable_source")]
    [InlineData("runlocal_self_source")]
    [InlineData("runlocal_inventory_failure")]
    [InlineData("runlocal_commit_failure")]
    [InlineData("runlocal_policy_refusal")]
    [InlineData("protocol_relative_batch")]
    public void CleanupContinuesAfterSourceDisposal(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests." + probe], root, TimeSpan.FromSeconds(90), 1024 * 1024,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void RunLocalCleanupUsesCommonWorktreePreservationQualification()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests.runlocal_consumer"], root, TimeSpan.FromSeconds(90), 1024 * 1024,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    public static IEnumerable<object[]> HostReclamationCases()
    {
        if (OperatingSystem.IsWindows())
        {
            yield return ["unsupported-platform", "unsupported-platform"];
            yield break;
        }
        var root = TestRepositoryLayout.FindRoot();
        foreach (var fixture in new[]
                 { "host_reclaim_tests.py", "host_remnant_tests.py", "host_remnant_isolation_tests.py",
                     "host_remnant_recovery_tests.py" })
        {
            var result = TestProcessRunner.Run("python3",
                ["-B", Path.Combine(root, "tools/tests/StrataLint.WorkflowScript.Tests/Fixtures", fixture),
                    root, "--list-tests"], root, TimeSpan.FromSeconds(120), 1024 * 1024);
            Assert.True(result.ExitCode == 0,
                Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
            var probes = JsonSerializer.Deserialize<string[]>(result.StandardOutput);
            Assert.NotNull(probes);
            Assert.NotEmpty(probes);
            Assert.Equal(probes.Length, probes.Distinct(StringComparer.Ordinal).Count());
            foreach (var probe in probes) yield return [fixture, probe];
        }
    }

    [Theory]
    [MemberData(nameof(HostReclamationCases))]
    public void HostReclamationProtectsDependenciesAndCoordinatesCacheWriters(string fixture, string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root, "tools/tests/StrataLint.WorkflowScript.Tests/Fixtures", fixture),
                root, probe],
            root, TimeSpan.FromSeconds(120), 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains("Ran 1 test", Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void RemnantBlueprintHistoryBeyondTipAndCommitSamplesIsRecoverable()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorkflowScript.Tests/Fixtures/host_remnant_recovery_tests.py"),
                root, "RemnantRecoveryTests.test_recovery_mixed_history_outside_tip_and_commit_samples"],
            root, TimeSpan.FromSeconds(120), 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains("Ran 1 test", Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void MissingChildDuringReclamationWarnsAndContinues()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root, "tools/tests/StrataLint.WorkflowScript.Tests/Fixtures/host_reclaim_tests.py"),
                root, "HostReclaimTests.test_partial_removal_warns_and_continues_with_successful_summary"],
            root, TimeSpan.FromSeconds(120), 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void CleanupAndWorktreePreflightMeetTheirBehaviorContract()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run(
            "python3",
            ["-B", Path.Combine(root, "tools/tests/StrataLint.WorkflowScript.Tests/Fixtures/host_cleanup_tests.py"),
                Path.Combine(root, "tools/scripts/host-cleanup.py")],
            root,
            TimeSpan.FromSeconds(120),
            1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
