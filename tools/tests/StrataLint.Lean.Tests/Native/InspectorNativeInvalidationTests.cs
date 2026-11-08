namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeInvalidationTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Each consumer scenario keeps its project cold and retains its supervisor guard.
    [Theory]
    [InlineData("test_native.NativeSemanticTests.test_exported_private_dependency_invalidates_report")]
    [InlineData("test_native.NativeSemanticTests.test_exported_transitive_dependency_binding")]
    [InlineData("test_native.NativeSemanticTests.test_literal_utility_refutation")]
    [InlineData("test_native.NativeSemanticTests.test_native_invalidation")]
    [InlineData("test_native.NativeSemanticTests.test_native_judge_compiler_dependency_scope")]
    [InlineData("test_native.NativeSemanticTests.test_private_transitive_definition_invalidates_utility")]
    [InlineData("test_native.NativeSemanticTests.test_reported_module_proof_axioms_invalidate_public_trace")]
    [InlineData("test_native.NativeCompilerTests.test_native_config_options_rebuild_and_fail_closed")]
    [InlineData("test_native.NativeCompilerTests.test_native_facet_supplies_toolchain_environment")]
    [InlineData("test_native.NativeCompilerTests.test_public_module_report_and_private_job_is_not_a_target")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);
}
