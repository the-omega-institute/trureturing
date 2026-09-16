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
    [InlineData("Contracts.test_parentless_checkout_needs_no_base_or_remote")]
    [InlineData("Contracts.test_reusable_input_cannot_fall_back_to_event_sha_when_empty")]
    [InlineData("Contracts.test_native_checkout_accepts_empty_actions_input_context")]
    [InlineData("Contracts.test_valid_actions_seed_still_enters_production_and_signals_release_skip")]
    [InlineData("Contracts.test_corruption_and_transfer_miss_reach_production_under_set_e")]
    [InlineData("Contracts.test_foreign_partition_is_a_miss_and_snapshot_save_failure_is_nonfatal")]
    [InlineData("Contracts.test_malformed_actions_manifest_cannot_stop_normal_production")]
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
    [InlineData("ci_contract", "test_large_layer_snapshot_copies_and_hashes_in_one_read")]
    [InlineData("ci_contract", "test_execution_snapshot_consumes_the_exporters_inventory")]
    [InlineData("ci_contract", "test_snapshot_late_read_failure_keeps_published_material_and_source")]
    [InlineData("ci_contract", "test_layer_filter_cannot_expand_registered_stage_scope")]
    [InlineData("ci_contract", "test_bounded_snapshot_publishes_only_after_worker_and_save_window")]
    [InlineData("ci_contract", "test_bounded_snapshot_timeout_and_signals_clean_only_owned_staging")]
    [InlineData("ci_contract", "test_bounded_snapshot_cleans_descendants_after_worker_exits")]
    [InlineData("ci_contract", "test_snapshot_publication_failure_restores_previous_seed")]
    [InlineData("ci_contract", "test_same_filesystem_restore_moves_validated_material_without_copy")]
    [InlineData("ci_contract", "test_same_filesystem_restore_rejects_extra_member_before_publication")]
    [InlineData("ci_contract", "test_same_filesystem_restore_allows_unlisted_empty_directory")]
    [InlineData("ci_contract", "test_same_filesystem_restore_rolls_back_install_failure_and_source")]
    [InlineData("ci_contract", "test_dependency_and_project_restore_read_each_material_once")]
    [InlineData("ci_contract", "test_dependency_and_project_reject_late_bad_material_without_installing")]
    [InlineData("ci_contract", "test_dependency_and_project_restore_rolls_back_on_rename_or_exdev")]
    [InlineData("ci_contract", "test_corrupt_cache_is_rejected_before_replacing_existing_target")]
    [InlineData("ci_contract", "test_dependency_module_and_submodule_seed_round_trip")]
    [InlineData("ci_contract", "test_project_module_and_submodule_seed_round_trip")]
    [InlineData("ci_contract", "test_internal_dependency_file_links_round_trip_as_private_material")]
    [InlineData("report_snapshot_contract", "test_invalid_dependency_links_disable_only_that_save_with_an_offending_path")]
    [InlineData("ci_contract", "test_corrupt_dependency_seed_falls_back_without_replacing_current_material")]
    [InlineData("report_snapshot_contract", "test_snapshot_readiness_and_material_follow_writer_permissions")]
    [InlineData("report_snapshot_contract", "test_native_report_is_normal_project_material")]
    [InlineData("report_snapshot_contract", "test_current_handoff_accepts_native_five_members_without_preparation")]
    [InlineData("report_snapshot_contract", "test_current_handoff_rejects_each_missing_or_damaged_member")]
    [InlineData("report_snapshot_contract", "test_current_handoff_rejects_wrong_execution_and_skipped_lean")]
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
