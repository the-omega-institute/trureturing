namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeInterfaceTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // The standalone Interface package checks use a class-owned compiler stage.
    [Theory]
    [InlineData("test_native.NativeTests.test_interface_standalone_core_only")]
    [InlineData("test_native.NativeTests.test_interface_only_reports_missing_handler")]
    [InlineData("test_native.NativeTests.test_interface_grammar_has_single_owner")]
    [InlineData("test_native.NativeTests.test_interface_registered_build_inputs")]
    [InlineData("test_native.NativeTests.test_interface_records_have_single_owner")]
    [InlineData("test_native.NativeTests.test_interface_store_cross_module_persistence")]
    [InlineData("test_native.NativeTests.test_interface_edit_rebuilds_implementation_consumer")]
    [InlineData("test_native.NativeTests.test_reg_empty_and_nonempty_build_routing")]
    [InlineData("test_native.NativeTests.test_reg_report_rows_relocation_and_defaults")]
    [InlineData("test_native.NativeTests.test_reg_manifest_rejected_before_materialization")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);
}
