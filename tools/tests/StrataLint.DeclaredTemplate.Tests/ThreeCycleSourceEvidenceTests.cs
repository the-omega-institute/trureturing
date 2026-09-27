namespace StrataLint.DeclaredTemplate.Tests;

public sealed class ThreeCycleSourceEvidenceTests
{
    [Fact]
    public void complete_original_passes_native_join_and_corruptions_reject() =>
        NamedCombinatoricsNativeFixture.Check("ShrunkenGrassmannianThreeCycleDiameter",
            "5f4dd168807b5f24bfb5a2a04ed81c51ef9342feb65c69a6ccfea8bfa16f142c", [0], true);
}
