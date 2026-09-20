using StrataLint.Engine;
using StrataLint.Scribe;
using System.Text.Json;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Theory]
    [InlineData("SL-015", "Reg/lake-manifest.json", false)]
    [InlineData("SL-015", "Reg/lakefile.toml", false)]
    [InlineData("SL-002", "Reg/Support/X.lean", true)]
    [InlineData("SL-020", "Reg/D5/S3/Arith/X.lean", true)]
    [InlineData("SL-003", "Reg/Support/X.lean", false)]
    [InlineData("SL-003", "Reg/lake-manifest.json", false)]
    public void RegChangesParticipateInCurrentCheckMaterials(string rule, string path, bool report)
    {
        using var json = JsonDocument.Parse(File.ReadAllBytes(
            Path.Combine(RepositoryLayout.FindRoot(), "Meta/ci-checks.json")));
        var check = json.RootElement.GetProperty("checks").EnumerateArray()
            .Single(item => item.GetProperty("id").GetString() == rule);
        Assert.Contains(check.GetProperty("materials").EnumerateArray(),
            item => FileMapGlob.Create(item.GetString()!).IsMatch(path));
        if (report)
            Assert.All(check.GetProperty("report_inputs").EnumerateArray(), input =>
                Assert.Contains(input.GetProperty("materials").EnumerateArray(),
                    item => FileMapGlob.Create(item.GetString()!).IsMatch(path)));
    }

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
