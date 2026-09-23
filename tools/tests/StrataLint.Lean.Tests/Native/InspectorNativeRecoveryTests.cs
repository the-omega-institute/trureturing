namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeRecoveryTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Recovery uses a separate, class-owned compiler stage.
    [Theory]
    [InlineData("test_native.NativeTests.test_release_stage_and_verify_preserve_absent_lake")]
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
}
