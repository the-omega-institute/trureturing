using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Theory]
    [InlineData("Reg/lakefile.toml", false)]
    [InlineData("Reg/lake-manifest.json", false)]
    [InlineData("Reg/D5/S3/Arith/X.lean", true)]
    [InlineData("Reg/Support/X.lean", true)]
    [InlineData("Reg/Catalogs/Family/X.lean", true)]
    public void RegPathsHaveExactlyOneEntry(string path, bool declaration)
    {
        var entry = Assert.Single(FileMapLoader.LoadRepository(RepositoryLayout.FindRoot()).Match(path));
        Assert.Equal(declaration ? FileMapKind.Data : FileMapKind.Program, entry.Kind);
        Assert.Equal(declaration ? FileMapAdmissionPlane.Content : FileMapAdmissionPlane.Judge, entry.AdmissionPlane);
        if (declaration)
        {
            Assert.Contains("lean-build", entry.VerifiedBy);
            Assert.Contains("lean-inspector", entry.VerifiedBy);
            Assert.DoesNotContain("Scribe", entry.ConsumedBy);
        }
    }
}
