namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeRecoveryTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Invalidation and recovery use a separate, class-owned compiler stage.
    [Theory]
    [InlineData("test_native.NativeTests.test_release_stage_and_verify_preserve_absent_lake")]
    [InlineData("test_native.NativeTests.test_native_no_build_rejects_corruption_without_production")]
    [InlineData("test_native.NativeTests.test_public_module_validates_and_private_job_is_not_a_target")]
    [InlineData("test_native.NativeTests.test_native_invalidation")]
    [InlineData("test_native.NativeTests.test_native_judge_semantic_version_gate")]
    [InlineData("test_native.NativeTests.test_native_config_options_rebuild_and_fail_closed")]
    [InlineData("test_native.NativeTests.test_reported_module_proof_axioms_invalidate_public_trace")]
    [InlineData("test_native.NativeTests.test_private_transitive_definition_invalidates_utility")]
    [InlineData("test_native.NativeTests.test_exported_transitive_dependency_binding")]
    [InlineData("test_native.NativeTests.test_exported_private_dependency_and_retired_origin")]
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
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);

    [Theory]
    [InlineData("test_native.NativeTests.test_native_module_validation_uses_lake_trace")]
    [InlineData("test_native.NativeTests.test_native_module_integrity_rejections")]
    [InlineData("test_native.NativeTests.test_imported_comment_warm_report_equals_fresh")]
    [InlineData("test_native.NativeTests.test_native_compatibility_preimage")]
    public void ModuleCacheValidation(string suite) => InspectorNativeTestRunner.Run(compiler, suite);

    [Fact]
    public void OldManifestKeyRejected() =>
        InspectorNativeTestRunner.Run(compiler, "test_native.NativeTests.test_native_old_manifest_key_rejected");

    [Fact]
    public void ModuleBindingScope() =>
        InspectorNativeTestRunner.Run(compiler, "test_native.NativeTests.test_native_module_binding_scope");
}
