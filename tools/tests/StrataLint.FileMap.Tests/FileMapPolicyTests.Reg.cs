using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.FileMap.Tests;

public sealed partial class FileMapPolicyTests
{
    [Theory]
    [InlineData("Reg/**/*.lean")]
    [InlineData("Reg/Unknown/**/*.lean")]
    public void OtherEmptyRegPatternsRemainRejected(string pattern)
    {
        var manifest = Parse(Entry(pattern, "data", "none", "Lean", "lean-build"));
        var finding = Assert.Single(FileMapPolicy.InspectPatternPopulation(manifest,
            [RegManifestAgreement.LakefilePath, RegManifestAgreement.ManifestPath]));
        Assert.Equal("FILEMAP-PATTERN-EMPTY", finding.Code);
    }

}
