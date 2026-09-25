namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeInvalidationTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Each complete consumer group prepares dependencies once and keeps every project cold.
    [Theory]
    [InlineData("test_native.NativeSemanticTests")]
    [InlineData("test_native.NativeCompilerTests")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);
}
