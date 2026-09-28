namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeEntryTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    [Fact]
    public void WholeReportReuseRequiresCurrentSemanticWitness() =>
        InspectorNativeTestRunner.Run(compiler, "test_native.NativeEntryTests");
}
