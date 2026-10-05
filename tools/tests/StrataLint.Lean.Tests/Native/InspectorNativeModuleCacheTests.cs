namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeModuleCacheTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Module cache validation uses a class-owned compiler stage.
    [Theory]
    [InlineData("test_native.NativeArtifactTests")]
    [InlineData("test_native.NativeTests.test_imported_comment_warm_report_equals_fresh")]
    [InlineData("test_native.NativeTests.test_native_compatibility_preimage")]
    [InlineData("test_native.NativeTests.test_native_typed_owner_version_scope")]
    public void ModuleCacheValidation(string suite) => InspectorNativeTestRunner.Run(compiler, suite);

    [Fact]
    public void CompiledOnlyReaderAndFailureBoundary() => InspectorNativeTestRunner.Run(compiler,
        "test_native.NativeTests.test_compiled_only_reader_and_failure_boundary");

    [Fact]
    public void OldManifestKeyRejected() =>
        InspectorNativeTestRunner.Run(compiler, "test_native.NativeTests.test_native_old_manifest_key_rejected");

    [Fact]
    public void ModuleBindingScope() =>
        InspectorNativeTestRunner.Run(compiler, "test_native.NativeTests.test_native_module_binding_scope");
}
