namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeRecoveryTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Recovery shares dependencies; each case still builds a private cold project.
    [Fact]
    public void InspectorArtifactBehavior() => InspectorNativeTestRunner.Run(compiler, "test_native.NativeRecoveryTests");

    [Fact]
    public void RuntimeBatchCapacity() => InspectorNativeTestRunner.Run(compiler, "test_native.NativeBatchCapacityTests");

    [Fact]
    public void RuntimeBatchCapacityConflictingOwners() => InspectorNativeTestRunner.Run(compiler,
        "test_native.NativeBatchCompatibilityTests.test_runtime_capacity_rejects_incompatible_sibling_constants");

    [Fact]
    public void RuntimeBatchCapacityCompatibleOwners() => InspectorNativeTestRunner.Run(compiler,
        "test_native.NativeBatchCompatibilityTests.test_runtime_capacity_accepts_compatible_duplicate_owners");
}
