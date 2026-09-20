namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeInvalidationTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Invalidation and dependency binding use a class-owned compiler stage.
    [Theory]
    [InlineData("test_native.NativeTests.test_declared_helper_comment_preserves_report_and_plan_identity")]
    [InlineData("test_native.NativeTests.test_native_no_build_rejects_corruption_without_production")]
    [InlineData("test_native.NativeTests.test_public_module_validates_and_private_job_is_not_a_target")]
    [InlineData("test_native.NativeTests.test_native_invalidation")]
    [InlineData("test_native.NativeTests.test_native_judge_semantic_version_gate")]
    [InlineData("test_native.NativeTests.test_native_config_options_rebuild_and_fail_closed")]
    [InlineData("test_native.NativeTests.test_reported_module_proof_axioms_invalidate_public_trace")]
    [InlineData("test_native.NativeTests.test_private_transitive_definition_invalidates_utility")]
    [InlineData("test_native.NativeTests.test_exported_transitive_dependency_binding")]
    [InlineData("test_native.NativeTests.test_exported_private_dependency_and_retired_origin")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);
}
