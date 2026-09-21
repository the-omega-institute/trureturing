using System.Text;

namespace StrataLint.Tests;

public sealed class LeanCacheInputScriptTests
{
    [Fact]
    public void TruthReleaseConsumesOnlySelectedValidatedPushBundles()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/truth_release_contract.py")],
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("Contracts.test_resolver_fixes_merge_and_first_parent_before_merge_ref_moves")]
    [InlineData("Contracts.test_resolver_reads_schema_two_filemap_only_for_the_immutable_base")]
    [InlineData("Contracts.test_parentless_checkout_needs_no_base_or_remote")]
    [InlineData("Contracts.test_reusable_input_cannot_fall_back_to_event_sha_when_empty")]
    [InlineData("Contracts.test_native_checkout_accepts_empty_actions_input_context")]
    [InlineData("Contracts.test_native_checkout_fetches_only_fixed_before_from_shallow_clone")]
    [InlineData("Contracts.test_valid_actions_seed_still_enters_production_and_signals_release_skip")]
    [InlineData("Contracts.test_corruption_and_transfer_miss_reach_production_under_set_e")]
    [InlineData("Contracts.test_foreign_partition_is_a_miss_and_snapshot_save_failure_is_nonfatal")]
    [InlineData("Contracts.test_missing_restored_directory_cannot_stop_normal_production")]
    [InlineData("Contracts.test_pull_request_cannot_publish_snapshot")]
    [InlineData("Contracts.test_pull_request_restores_seed_with_writes_disabled")]
    [InlineData("Contracts.test_transport_delegates_to_common_owner_without_a_package_cache")]
    [InlineData("LegacyCallerTests.test_gate_preserves_checks_and_annotation_with_candidate_runtime")]
    [InlineData("LegacyCallerTests.test_gate_build_failure_stops_before_checks")]
    [InlineData("LegacyCallerTests.test_judge_address_uses_real_pinned_runtime_and_source")]
    public void ImmutableResolutionAndOptionalActionsSeeds(string behavior)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/ci_contract.py"),
                behavior],
            root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("cache_snapshot_contract", "test_native_restore_requires_success_and_the_selected_partition")]
    [InlineData("cache_snapshot_contract", "test_unexecuted_action_preserves_current_evidence_and_cannot_claim_a_seed")]
    [InlineData("cache_snapshot_contract", "test_success_without_a_matched_key_discards_partial_action_extraction")]
    [InlineData("cache_snapshot_contract", "test_success_without_restored_directory_is_a_miss")]
    [InlineData("cache_snapshot_contract", "test_dependency_retention_uses_only_registered_small_inputs_after_successful_restore")]
    [InlineData("cache_snapshot_contract", "test_dependency_retention_requires_this_round_and_an_accepted_small_receipt")]
    [InlineData("cache_snapshot_contract", "test_project_updates_after_each_successful_production_even_with_an_unchanged_report")]
    [InlineData("cache_snapshot_contract", "test_bounded_snapshot_authorizes_only_inside_the_remaining_save_window")]
    [InlineData("cache_snapshot_contract", "test_native_metadata_save_failure_keeps_produced_material")]
    [InlineData("cache_snapshot_contract", "test_native_actions_paths_are_the_registered_build_directories")]
    [InlineData("cache_snapshot_contract", "test_native_project_authorization_preserves_outputs_without_directory_reads")]
    [InlineData("cache_snapshot_contract", "test_staged_restore_subset_cannot_expand_the_registered_cache_layers")]
    [InlineData("cache_snapshot_contract", "test_layer_filter_cannot_expand_registered_stage_scope")]
    [InlineData("cache_snapshot_contract", "test_bounded_snapshot_cleans_descendants_after_worker_exits")]
    [InlineData("cache_snapshot_contract", "test_execution_snapshot_consumes_the_exporters_inventory")]
    [InlineData("cache_snapshot_contract", "test_judge_restore_rejects_late_changes_without_replacing_target")]
    [InlineData("report_snapshot_contract", "test_report_route_uses_only_declared_complete_receipts_and_never_publishes")]
    [InlineData("report_snapshot_contract", "test_report_route_missing_seed_does_not_invoke_a_producer_or_claim_success")]
    [InlineData("report_snapshot_contract", "test_report_preparation_restores_only_current_and_keeps_normal_producer_selected")]
    [InlineData("report_snapshot_contract", "test_native_report_is_normal_project_material")]
    [InlineData("report_snapshot_contract", "test_current_handoff_accepts_native_five_members_without_directory_scans")]
    [InlineData("report_snapshot_contract", "test_current_handoff_rejects_each_missing_or_damaged_member")]
    [InlineData("report_snapshot_contract", "test_current_handoff_rejects_wrong_execution_and_skipped_lean")]
    [InlineData("report_snapshot_contract", "test_snapshot_readiness_and_material_follow_writer_permissions")]
    public void SnapshotReadinessAndMaterialRespectWriterPermissions(string fixture, string behavior)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures", fixture + ".py"), "SnapshotContracts." + behavior],
            root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void ResolvedMathlibPartitionBehavior()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/lean_input_contract.py"), "PartitionTests"],
            root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
