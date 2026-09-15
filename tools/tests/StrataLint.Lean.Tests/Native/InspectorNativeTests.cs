using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeTests
{
    [Theory]
    [InlineData("test_streaming")]
    [InlineData("test_native.NativeTests.test_coordinates_use_private_temporary_memo_and_clean_up_failures")]
    [InlineData("test_native.NativeTests.test_coordinates_reuse_warm_tree_memo")]
    [InlineData("test_native.NativeTests.test_input_verification_is_read_only")]
    [InlineData("test_native.NativeTests.test_release_stage_and_verify_preserve_absent_lake")]
    [InlineData("test_native.NativeTests.test_native_no_build_rejects_corruption_without_production")]
    [InlineData("test_native.NativeTests.test_publication_validates_material_identities_once")]
    [InlineData("test_native.NativeTests.test_native_publication_rejects_incoming_damage_before_normalization")]
    [InlineData("test_native.NativeTests.test_publication_snapshot_integrity_and_replace_failure")]
    [InlineData("test_native.NativeTests.test_public_module_validates_and_private_job_is_not_a_target")]
    [InlineData("test_native.NativeTests.test_native_invalidation")]
    [InlineData("test_native.NativeTests.test_native_config_options_rebuild_and_fail_closed")]
    [InlineData("test_native.NativeTests.test_reported_module_proof_axioms_invalidate_public_trace")]
    [InlineData("test_native.NativeTests.test_private_transitive_definition_invalidates_utility")]
    [InlineData("test_native.NativeTests.test_exported_transitive_dependency_binding")]
    [InlineData("test_native.NativeTests.test_exported_private_dependency_and_missing_binding")]
    [InlineData("test_native.NativeTests.test_native_producer_inputs")]
    [InlineData("test_native.NativeTests.test_native_semantic_version_and_config")]
    [InlineData("test_native.NativeTests.test_native_invalid_semantic_versions")]
    [InlineData("test_native.NativeTests.test_native_recovery_and_required_failures")]
    [InlineData("test_native.NativeTests.test_native_recovers_only_row_with_damaged_deflate")]
    [InlineData("test_native.NativeTests.test_native_recovers_only_row_with_damaged_lzma")]
    [InlineData("test_native.NativeTests.test_native_recovers_outer_member_without_lzma")]
    [InlineData("test_native.NativeTests.test_native_recovers_nested_material_without_lzma")]
    [InlineData("test_native.NativeTests.test_native_optional_lzma_and_batch_failure_boundaries")]
    [InlineData("test_native.NativeTests.test_native_recovers_only_row_with_unsupported_compression")]
    [InlineData("test_native.NativeTests.test_native_recovers_only_row_with_encrypted_member")]
    [InlineData("test_native.NativeTests.test_native_recovers_only_row_with_encrypted_material")]
    [InlineData("test_native.NativeTests.test_native_recovers_encrypted_report")]
    [InlineData("test_native.NativeTests.test_native_pack_unpack_reuses_complete_rows")]
    [InlineData("test_native.NativeTests.test_native_clonefile_seed_reuses_rows_and_keeps_donor_private")]
    [InlineData("test_native.NativeTests.test_snapshot_generation_preserves_mathlib_partition")]
    public void InspectorArtifactBehavior(string suite)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", "-m", "unittest", suite, "-v"],
            Path.Combine(root, "tools/lean-inspector/tests"), TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }
}
