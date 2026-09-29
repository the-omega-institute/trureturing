namespace StrataLint.DeclaredTemplate.Tests;

public sealed class LatticeWalkSourceEvidenceTests
{
    [Fact]
    public void exact_frozen_original_passes_native_join_and_corruptions_reject() =>
        NamedCombinatoricsNativeFixture.Check("LatticeWalkNearMaximalArea", "b173b45d15afd3b9fece681fc969b66ec8a2ff98920ecf7c0cca8b061e646f48", [], true);
}
