namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeRecoveryTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Each recovery case retains a private cold project and its supervisor guard.
    [Theory]
    [InlineData("test_native.NativeRecoveryTests.test_compatibility_call_uses_raw_reader_without_publishing_rows")]
    [InlineData("test_native.NativeRecoveryTests.test_completed_chunk_survives_later_cancellation")]
    [InlineData("test_native.NativeRecoveryTests.test_completed_chunk_survives_later_failure")]
    [InlineData("test_native.NativeRecoveryTests.test_completed_chunk_survives_later_truncation")]
    [InlineData("test_native.NativeRecoveryTests.test_failed_split_compatibility_prevents_extraction")]
    [InlineData("test_native.NativeRecoveryTests.test_native_imports_without_lzma_and_batch_failures_propagate")]
    [InlineData("test_native.NativeRecoveryTests.test_native_required_failures")]
    [InlineData("test_native.NativeRecoveryTests.test_partition_binds_reg_sized_inventory")]
    [InlineData("test_native.NativeRecoveryTests.test_partition_preserves_membership_and_order")]
    [InlineData("test_native.NativeRecoveryTests.test_partition_rejects_cross_chunk_duplicate_and_mixed_owner")]
    [InlineData("test_native.NativeRecoveryTests.test_release_stage_and_verify_preserve_absent_lake")]
    [InlineData("test_native.NativeRecoveryTests.test_runtime_capacity_bounds_each_raw_and_judged_group")]
    [InlineData("test_native.NativeRecoveryTests.test_split_assessment_failure_preserves_legacy_publication_boundary")]
    [InlineData("test_native.NativeRecoveryTests.test_split_compatibility_keeps_fixed_windows_and_raw_judged_boundaries")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);

    [Fact]
    public void RuntimeBatchCapacity() => InspectorNativeTestRunner.Run(compiler, "test_native.NativeBatchCapacityTests");

    [Fact]
    public void RuntimeBatchCapacityConflictingOwners() => InspectorNativeTestRunner.Run(compiler,
        "test_native.NativeBatchCompatibilityTests.test_runtime_capacity_rejects_incompatible_sibling_constants");

    [Fact]
    public void RuntimeBatchCapacityCompatibleOwners() => InspectorNativeTestRunner.Run(compiler,
        "test_native.NativeBatchCompatibilityTests.test_runtime_capacity_accepts_compatible_duplicate_owners");
}
