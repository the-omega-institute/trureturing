namespace StrataLint.Lean.Tests;

public sealed class InspectorNativePackagingTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Producer inputs, seeds, packaging and release partitions use a class-owned compiler stage.
    [Theory]
    [InlineData("test_native.NativeTests.test_native_compiler_seed_is_private")]
    [InlineData("test_native.NativeTests.test_snapshot_generation_preserves_mathlib_partition")]
    [InlineData("test_native.NativeTests.test_release_partition_preserves_semantic_and_selection_changes")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);

    [Fact]
    public void PackageConsumersStartWithPrivateColdProjects() => InspectorNativeTestRunner.Run(compiler,
        "test_native.NativePackageTests");

    [Fact]
    public void WorkloadRejectsNonfixtureBeforeWrites() => InspectorNativeTestRunner.Run(compiler,
        "test_native.NativeTests.test_native_workload_rejects_nonfixture_before_writes");
}
