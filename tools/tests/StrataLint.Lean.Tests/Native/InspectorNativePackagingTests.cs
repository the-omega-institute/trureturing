namespace StrataLint.Lean.Tests;

public sealed class InspectorNativePackagingTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Producer inputs, seeds, packaging and release partitions use a class-owned compiler stage.
    [Theory]
    [InlineData("test_native.NativeTests.test_native_producer_inputs")]
    [InlineData("test_native.NativeTests.test_native_compiler_seed_is_private")]
    [InlineData("test_native.NativeTests.test_native_semantic_version_and_config")]
    [InlineData("test_native.NativeTests.test_native_invalid_semantic_versions")]
    [InlineData("test_native.NativeTests.test_native_pack_unpack_reuses_complete_rows")]
    [InlineData("test_native.NativeTests.test_native_clonefile_seed_reuses_rows_and_keeps_donor_private")]
    [InlineData("test_native.NativeTests.test_snapshot_generation_preserves_mathlib_partition")]
    [InlineData("test_native.NativeTests.test_release_publisher_legacy_seed_current_pack_restore_and_unchanged")]
    [InlineData("test_native.NativeTests.test_release_partition_preserves_semantic_and_selection_changes")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);
}
