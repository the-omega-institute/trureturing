namespace StrataLint.DeclaredTemplate.Tests;

public sealed class ConjectureSixteenSourceEvidenceTests
{
    [Fact]
    public void complete_negative_original_passes_native_join_and_corruptions_reject() =>
        NamedCombinatoricsNativeFixture.Check("ShrunkenGrassmannianConjectureSixteenRefutation",
            "31b70712feedc13b36b71270e679d7b7dace55e37db536230ed8a1573552059b", [], true);
}
