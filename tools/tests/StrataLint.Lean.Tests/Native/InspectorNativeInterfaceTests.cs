namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeInterfaceTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // The standalone Interface package checks use a class-owned compiler stage.
    [Theory]
    [InlineData("test_native.NativeTests.test_interface_standalone_core_only")]
    [InlineData("test_native.NativeTests.test_interface_typed_inputs_compile_without_judge")]
    [InlineData("test_native.NativeTests.test_interface_registered_build_inputs")]
    [InlineData("test_native.NativeTests.test_output_audit_follows_compiler_package_owners")]
    [InlineData("test_native.NativeTests.test_reg_manifest_rejected_before_materialization")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);

    [Fact]
    public void RoutingConsumersStartWithPrivateColdProjects() => InspectorNativeTestRunner.Run(compiler,
        "test_native.NativeRoutingTests");
}
