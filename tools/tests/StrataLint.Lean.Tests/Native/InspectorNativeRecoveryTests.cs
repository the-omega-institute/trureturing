namespace StrataLint.Lean.Tests;

[Collection("Lean cold production integration")]
public sealed class InspectorNativeRecoveryTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Recovery shares dependencies; each case still builds a private cold project.
    [Fact]
    public void InspectorArtifactBehavior() => InspectorNativeTestRunner.Run(compiler, "test_native.NativeRecoveryTests");
}
