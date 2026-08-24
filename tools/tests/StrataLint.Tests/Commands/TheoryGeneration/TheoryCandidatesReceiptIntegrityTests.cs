using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryCandidatesTests
{
    [Fact]
    public void ReceiptIntegrityGapRejectsTheoryCandidateProjection()
    {
        var fixture = CandidateFixture();
        fixture.Files[PartialAtomPath] = fixture.Files[PartialAtomPath].Replace(
            "coverage: []",
            "coverage:\n"
            + "    - gid: D5/X_Frontier/FrontierMathematicalOpen\n"
            + $"      source_sha256: {RuleFixture.FixtureCasReference}\n"
            + "      target_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000",
            StringComparison.Ordinal);

        var result = Run(fixture);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Contains("coverage-receipt-mismatch", result.Error, StringComparison.Ordinal);
    }
}
