using System.Text;
using System.Text.Json;
using Xunit.Abstractions;
using StrataLint.Runtime;
using StrataLint.Engine;
using Xunit;

namespace StrataLint.WorktreeContract.Tests;

public sealed class WorktreeProtocolTests(ITestOutputHelper output)
{
    [Fact]
    public void CleanupFixtureCopiesActualSourceInputs()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, "plain", "clean-lanes", "directory", "SourceCopyTests"],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("spaced", "clean-lanes", "directory")]
    [InlineData("spaced", "clean-all", "directory")]
    [InlineData("spaced", "worktree-clean", "directory")]
    [InlineData("spaced", "clean-lanes", "file")]
    [InlineData("spaced", "clean-all", "file")]
    [InlineData("plain", "clean-lanes", "directory")]
    [InlineData("plain", "clean-all", "directory")]
    [InlineData("plain", "worktree-clean", "directory")]
    public void CleanupMakeEntrancesUseProductionQualification(string sourcePath, string entrance, string invocation)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, sourcePath, entrance, invocation, "CleanupMakeTests.test_production_cleanup_entrances"],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("self")]
    [InlineData("stable")]
    [InlineData("missing")]
    [InlineData("divergent")]
    public void AggregateCleanupSurvivesRepositoryRemoval(string invocation)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, "spaced", "clean-all", invocation,
                "CleanupMakeTests.test_aggregate_survives_repository_removal"],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("clean-lanes", "self")]
    [InlineData("clean-lanes", "missing")]
    [InlineData("clean-lanes", "divergent")]
    [InlineData("worktree-remove", "divergent")]
    public void RegisteredCleanupSurvivesCallerRemoval(string entrance, string invocation)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, "spaced", entrance, invocation,
                "CleanupMakeTests.test_registered_consumer_survives_source_removal"],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("normal")]
    [InlineData("nonzero")]
    [InlineData("deadline")]
    [InlineData("launcher")]
    public void CleanupFixtureSettlesOwnedNativeCommands(string mode)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, "plain", "clean-lanes", "directory", "CommandLifetimeTests.test_" + mode],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void NativeSignalErrorsDoNotPrematurelyEndOwnedSettlement()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, "plain", "clean-lanes", "directory", "SignalErrorTests.test_delivery_error",
                "SignalErrorTests.test_observation_error"],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void FixtureDisposalWaitsForCompleteOutcomeAndNativeSettlement()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, "plain", "clean-lanes", "directory", "FixtureDisposalTests"],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void OuterInterruptionRetainsFailedInputsAndPublishesOwnedGroupSettlement()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var captured = new List<string>();
        var failure = Assert.Throws<SkipException>(() => CaptureCleanupOutput((stdout, stderr) =>
            TestProcessRunner.Run("python3", ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, "plain", "clean-lanes", "directory", "CommandLifetimeTests.test_deadline"],
                root, TimeSpan.FromSeconds(3), 1024 * 1024,
                standardOutput: stdout, standardError: stderr,
                interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), captured.Add));
        Assert.StartsWith(InfrastructureHangGuard.SkipReasonPrefix, failure.Message);
        foreach (var value in captured) output.WriteLine(value);
        var events = captured[0].Split('\n').Where(line => line.StartsWith('{'))
            .Select(line => JsonDocument.Parse(line).RootElement.Clone()).ToArray();
        var command = Assert.Single(events, item => item.GetProperty("event").GetString() == "fixture_command"
            && item.GetProperty("status").GetString() == "interrupted");
        Assert.True(command.GetProperty("settled").GetBoolean());
        Assert.Equal(120, command.GetProperty("guard_seconds").GetInt32());
        var completion = Assert.Single(events, item => item.GetProperty("event").GetString() == "fixture_completion");
        Assert.False(completion.GetProperty("successful").GetBoolean());
        Assert.True(completion.GetProperty("commands_settled").GetBoolean());
        Assert.True(completion.GetProperty("interrupted").GetBoolean());
        var inputs = completion.GetProperty("inputs").EnumerateArray().Select(item => item.GetString()!).ToArray();
        foreach (var path in inputs) Assert.True(Directory.Exists(path));
        var group = command.GetProperty("pid").GetInt32().ToString(System.Globalization.CultureInfo.InvariantCulture);
        var native = TestProcessRunner.Run("python3",
            ["-c", "import os,sys; os.killpg(int(sys.argv[1]),0)", group], root, TimeSpan.FromSeconds(10), 4096);
        Assert.NotEqual(0, native.ExitCode);
        Assert.Contains("ProcessLookupError", Encoding.UTF8.GetString(native.StandardError), StringComparison.Ordinal);
        foreach (var path in inputs) Directory.Delete(path, recursive: true);
    }

    private static ProcessOutput CaptureCleanupOutput(
        Func<Stream, Stream, ProcessOutput> run, Action<string> publish)
    {
        using var stdout = new MemoryStream();
        using var stderr = new MemoryStream();
        using var stdoutSink = Stream.Synchronized(stdout);
        using var stderrSink = Stream.Synchronized(stderr);
        try
        {
            return run(stdoutSink, stderrSink);
        }
        finally
        {
            // The runner can throw before returning its buffered ProcessOutput.
            // Its existing destinations preserve bytes already read on every exit path.
            lock (stdout) publish(Encoding.UTF8.GetString(stdout.ToArray()));
            lock (stderr) publish(Encoding.UTF8.GetString(stderr.ToArray()));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CleanupFixturePublishesEvidenceBeforeOuterGuardReturns(bool deadline)
    {
        if (OperatingSystem.IsWindows()) return;
        var captured = new List<string>();
        var root = TestRepositoryLayout.FindRoot();
        ProcessOutput Run(Stream stdout, Stream stderr) => TestProcessRunner.Run("/bin/sh",
            ["-c", "printf 'phase=owned-command partial-output\\n'; " +
                "printf 'partial-error\\n' >&2; " + (deadline ? "exec sleep 600" : "exit 7")],
            root, TimeSpan.FromSeconds(1), 1024 * 1024,
            standardOutput: stdout, standardError: stderr);
        if (deadline)
        {
            var failure = Assert.Throws<SkipException>(() => CaptureCleanupOutput(Run, captured.Add));
            Assert.StartsWith(InfrastructureHangGuard.SkipReasonPrefix, failure.Message);
        }
        else
        {
            Assert.Equal(7, CaptureCleanupOutput(Run, captured.Add).ExitCode);
        }
        Assert.Equal(["phase=owned-command partial-output\n", "partial-error\n"], captured);
        foreach (var item in captured) output.WriteLine(item);
    }

    [Theory]
    [InlineData("git_scope_rejects_operational_symbolic_ref_errors")]
    [InlineData("git_scope_symbolic_ref_failure_retains_removal")]
    [InlineData("git_scope_symbolic_ref_failure_fails_pool_inspection")]
    [InlineData("git_scope_symbolic_ref_failure_stops_pool_claim")]
    [InlineData("git_scope_symbolic_ref_failure_stops_pool_return")]
    [InlineData("git_scope_symbolic_ref_failure_stops_commands")]
    [InlineData("test_clean_detached_recovery")]
    [InlineData("test_dirty_detached_recovery")]
    public void GitScopeClassifiesSymbolicRefFailures(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests." + probe], root, TestBudgets.ProtocolProbeHangGuard, 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("qualification_intentional_lock_metadata_races")]
    [InlineData("pool_revalidation_keeps_refusal_and_prior_eviction")]
    [InlineData("pool_removal_qualification_preserves_refusal_and_operational_failure")]
    [InlineData("pool_return_selected_eviction_refusal_fails_public_exit")]
    [InlineData("pool_final_qualification_defers_later_candidates")]
    [InlineData("pool_return_final_qualification_defers_later_candidates")]
    [InlineData("pool_claim_qualification_failure_cannot_become_no_idle")]
    [InlineData("pool_scope_operational_failure_is_failed")]
    [InlineData("qualification_process_boundary_distinguishes_operational_errors")]
    [InlineData("qualification_native_identity_races_are_refused")]
    [InlineData("native_identity_races_are_refused")]
    [InlineData("qualification_stream_preserves_completed_and_defers_unreached")]
    [InlineData("runlocal_final_qualification_refusal")]
    [InlineData("runlocal_final_qualification_failure")]
    [InlineData("batch_qualification_preserves_each_reason_and_tree")]
    [InlineData("batch_qualification_reports_errors_without_hiding_other_results")]
    [InlineData("recovery_resolved_conflict_does_not_veto_removal")]
    [InlineData("recovery_published_prior_commit_message_is_reconstructable")]
    [InlineData("recovery_local_repository_is_not_a_remote")]
    [InlineData("recovery_checkpoint_protects_message_reads")]
    public void RecoveryQualificationUsesActualIndexAndCommitObjects(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests." + probe], root, TimeSpan.FromSeconds(90), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("scoped_git_configuration_disables_background_git")]
    [InlineData("native_lock_inspector_receives_scoped_environment")]
    [InlineData("timed_out_git_releases_index_lock")]
    public void ScopedGitLeavesNoLockHolderBehind(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests." + probe], root, TestBudgets.ProtocolProbeHangGuard, 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("mirror_operation_publishes_then_qualifies_removal")]
    [InlineData("mirror_failure_retains_conflict_and_failed_publication")]
    [InlineData("mirror_missing_endpoint_refused_before_creation")]
    [InlineData("mirror_only_target_delta_with_missing_merge_and_squash")]
    [InlineData("mirror_validator_rejects_wrong_delta_identity_parent_and_base")]
    [InlineData("mirror_retained_commit_reused_on_descendant_integration_base")]
    [InlineData("consumer_mirror_uses_real_git_with_stubbed_github")]
    [InlineData("consumer_land_commits_snapshot_with_external_checks_stubbed")]
    [InlineData("consumer_land_cannot_build_during_exclusive_operation")]
    [InlineData("consumer_land_scopes_operating_children")]
    public void AgentConsumerUsesRealGitAndPreservesIndependentMaterial(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests." + probe], root, TimeSpan.FromSeconds(90), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("pool_return_preserves_post_merge_work_branch_and_cache")]
    [InlineData("pool_unused_created_tree_returns_without_pr")]
    [InlineData("pool_unused_claimed_tree_returns_without_pr")]
    [InlineData("pool_unused_return_refuses_task_tip")]
    [InlineData("pool_unused_return_accepts_commit_then_reset")]
    [InlineData("pool_unused_return_refuses_dirty_content")]
    [InlineData("pool_unused_return_keeps_join_scope_lock_and_operation_guards")]
    [InlineData("pool_unused_return_refuses_missing_creation_evidence")]
    [InlineData("pool_unused_return_accepts_selectively_expired_task_history")]
    [InlineData("pool_unused_return_refuses_partially_expired_creation")]
    [InlineData("pool_unused_return_uses_creation_record_only")]
    [InlineData("pool_unused_return_refuses_invalid_creation_record")]
    [InlineData("pool_unused_return_refuses_already_idle_without_pr")]
    [InlineData("pool_unused_return_accepts_internal_cr_in_identity")]
    [InlineData("pool_unused_return_requires_remote_dev_retention")]
    [InlineData("pool_scope_contention_has_no_tree_effect")]
    [InlineData("pool_implicit_claim_busy_has_no_allocation")]
    [InlineData("pool_return_checkpoint_without_native_lock_never_inspects_holders")]
    [InlineData("pool_return_checkpoint_reports_cleared_native_locks")]
    [InlineData("pool_return_requires_join_and_real_merge_evidence")]
    [InlineData("pool_return_refuses_unretained_merge_wrong_head_and_busy_writer")]
    [InlineData("pool_return_refuses_conflicts_operations_and_main")]
    [InlineData("pool_claim_writes_immutable_allocation_and_preserves_cache")]
    [InlineData("pool_claim_requires_matching_pins_and_clean_idle_attachment")]
    [InlineData("pool_claim_accepts_returned_tip_ahead_of_tracking_dev")]
    [InlineData("pool_claim_refuses_exact_symlink")]
    [InlineData("pool_claim_concurrency_has_one_winner")]
    [InlineData("pool_capacity_and_pressure_use_one_owner")]
    [InlineData("pool_return_accepts_squash_and_merge_histories")]
    [InlineData("pool_sweep_confirms_returned_tip_beyond_stale_tracking")]
    [InlineData("pool_sweep_refuses_non_dev_idle_tip")]
    [InlineData("pool_eviction_failures_preserve_receipt_and_exit")]
    [InlineData("pool_idle_prefixed_task_is_never_released_by_allocation")]
    [InlineData("pool_validation_failure_after_eviction_preserves_receipt")]
    [InlineData("pool_return_validation_failure_after_eviction_preserves_receipt")]
    [InlineData("pool_pressure_failure_after_eviction_preserves_receipt")]
    [InlineData("pool_confirmation_timeout_after_eviction_preserves_receipt")]
    [InlineData("pool_unexpected_removal_failure_preserves_recovery")]
    public void IdlePoolPreservesNativeGitState(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests." + probe], root, TestBudgets.ProtocolProbeHangGuard, 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("holderless_native_locks_checkpoint_once")]
    [InlineData("detached_head_native_lock_can_recover_snapshot")]
    [InlineData("held_native_lock_retains_exact_blocker")]
    [InlineData("unverifiable_and_replaced_native_lock_retained")]
    [InlineData("native_lock_failure_receipts_keep_lock_observations")]
    [InlineData("native_clearance_requires_exclusive_tree")]
    [InlineData("dead_initializer_is_removable_without_lock_age")]
    [InlineData("live_initializer_is_retained")]
    [InlineData("native_clearance_keeps_dead_initializer_exclusive_until_removal")]
    [InlineData("failed_initialization_recovers_in_place_idempotently")]
    [InlineData("large_initialization_checkout_preserves_partial_bytes")]
    [InlineData("owned_unregistered_branch_can_resume")]
    [InlineData("ordinary_recovery_routing_keeps_shared_reuse_and_base_protection")]
    [InlineData("partial_registration_repairs_worktree_head_in_its_own_ref_store")]
    [InlineData("native_clearance_survives_failed_checkpoint_retry")]
    [InlineData("reconvergence_receipt_retains_native_clearance")]
    [InlineData("resume_validates_and_coordinates_recorded_predecessors")]
    [InlineData("initialization_identity_changes_refuse_recovery")]
    [InlineData("removal_record_mismatch_reconverges_and_keeps_both_roots")]
    [InlineData("reconvergence_interruption_retains_record_and_recovery_objects")]
    public void LockTaxonomyAndRecoveryPreserveBothSnapshots(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests.test_" + probe], root, TimeSpan.FromSeconds(90), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("removal_payload_failure_retains_registration_and_resumes")]
    [InlineData("removal_payload_process_death_retains_registration_and_resumes")]
    [InlineData("native_unregistration_failure_leaves_only_git_link")]
    [InlineData("removal_refuses_nested_repository_before_any_payload")]
    [InlineData("removal_refuses_gitlink_before_any_payload")]
    [InlineData("removal_refuses_submodule_before_any_payload")]
    [InlineData("removal_refuses_foreign_worktree_before_any_payload")]
    [InlineData("removal_refuses_bare_repository_before_any_payload")]
    [InlineData("removal_resumes_after_worktree_ignore_is_deleted")]
    [InlineData("removal_with_deleted_ignore_retains_new_ordinary_file")]
    public void RemovalKeepsRegistrationUntilPayloadIsGone(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests.test_" + probe], root, TimeSpan.FromSeconds(90), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    public void CooperativeProtocolPreservesRealProcessAndGitState(int part)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"), root,
                "--part", part.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
