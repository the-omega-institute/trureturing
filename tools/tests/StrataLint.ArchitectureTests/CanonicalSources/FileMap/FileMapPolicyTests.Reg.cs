using StrataLint.Engine;
using StrataLint.Cli;
using StrataLint.Scribe;
using System.Text.Json;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void EmptyRegPackagePassesRepositoryFileMapConformance()
    {
        Assert.Empty(FileMapPolicy.InspectRepository(RepositoryLayout.FindRoot()));
    }

    [Theory]
    [InlineData(null, 0)]
    [InlineData("Reg/lakefile.toml", 3)]
    [InlineData("Reg/lake-manifest.json", 3)]
    public void EmptyRegFamiliesRequireBothRegisteredPackageFiles(string? missing, int expected)
    {
        var manifest = FileMapLoader.LoadRepository(RepositoryLayout.FindRoot());
        string[] configs = [RegManifestAgreement.LakefilePath, RegManifestAgreement.ManifestPath];
        var findings = FileMapPolicy.InspectPatternPopulation(manifest, configs.Where(path => path != missing));
        Assert.Equal(expected, findings.Count(finding =>
            finding.Path.StartsWith("Reg/", StringComparison.Ordinal) && finding.Path.EndsWith(".lean", StringComparison.Ordinal)));
    }

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

    [Theory]
    [InlineData("lean-build", "tools/scripts/worktree/lean-cache-run.sh")]
    [InlineData("lean-inspector", "tools/lean-inspector/inspect.sh")]
    public void RegLeanVerifiersRequireTheirRegisteredImplementation(string verifier, string implementation)
    {
        var manifest = FileMapLoader.LoadRepository(RepositoryLayout.FindRoot());
        Assert.Contains(verifier, FileMapPolicy.AvailableDataVerifiers(manifest,
            new HashSet<string>(StringComparer.Ordinal) { implementation }));
        Assert.DoesNotContain(verifier, FileMapPolicy.AvailableDataVerifiers(manifest,
            new HashSet<string>(StringComparer.Ordinal)));
        var dataOnly = Parse(Entry("Reg/D5/**/*.lean", "data", "none", "Lean", verifier));
        Assert.DoesNotContain(verifier, FileMapPolicy.AvailableDataVerifiers(dataOnly,
            new HashSet<string>(StringComparer.Ordinal) { implementation }));
    }

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
