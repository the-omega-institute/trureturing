namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeInterfaceTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // The standalone Interface package checks use a class-owned compiler stage.
    [Theory]
    [InlineData("test_native.NativeTests.test_interface_standalone_core_only")]
    [InlineData("test_native.NativeTests.test_interface_typed_inputs_compile_without_judge")]
    [InlineData("test_native.NativeTests.test_interface_registered_build_inputs")]
    [InlineData("test_native.NativeTests.test_reg_manifest_rejected_before_materialization")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);

    [Theory]
    [InlineData("test_native.NativeRoutingTests.test_raw_interface_edit_breaks_reg_consumer")]
    [InlineData("test_native.NativeRoutingTests.test_reg_empty_and_nonempty_build_routing")]
    [InlineData("test_native.NativeRoutingTests.test_reg_report_rows_relocation_and_defaults")]
    [InlineData("test_native.NativeRoutingTests.test_shared_inspector_and_audit_build_reuses_native_programs")]
    public void RoutingConsumersStartWithPrivateColdProjects(string suite) =>
        InspectorNativeTestRunner.Run(compiler, suite);
}
