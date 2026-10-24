namespace StrataLint.Lean.Tests;

[Collection("Lean cold production integration")]
public sealed class InspectorNativeInvalidationTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Each complete consumer group prepares dependencies once and keeps every project cold.
    [Theory]
    [InlineData("test_native.NativeCompilerTests")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);

    public static IEnumerable<object[]> SemanticCases() => InspectorNativeTestRunner.Cases("test_native.NativeSemanticTests");

    [Theory]
    [MemberData(nameof(SemanticCases))]
    public void SemanticBehavior(string test) => InspectorNativeTestRunner.Run(compiler, test);
}
