namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeModuleCacheTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Module cache validation uses a class-owned compiler stage.
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
