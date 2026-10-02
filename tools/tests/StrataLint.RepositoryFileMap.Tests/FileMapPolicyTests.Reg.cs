using StrataLint.Scribe.Documents;
using System.Collections.Immutable;
using StrataLint.Engine;
using StrataLint.FileMap;
using StrataLint.Scribe;
using System.Text.Json;
using StrataLint.EngineeringScope;

namespace StrataLint.RepositoryFileMap.Tests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void EmptyRegPackagePassesRepositoryFileMapConformance()
    {
        Assert.Empty(FileMapPolicy.InspectRepository(TestRepositoryLayout.FindRoot(),
            DocumentAssembly.Definitions.Select(definition => definition.RelativePath.Value)));
    }

    [Theory]
    [InlineData(null, 0)]
    [InlineData("Reg/lakefile.toml", 3)]
    [InlineData("Reg/lake-manifest.json", 3)]
    public void EmptyRegFamiliesRequireBothRegisteredPackageFiles(string? missing, int expected)
    {
        var manifest = FileMapLoader.LoadRepository(TestRepositoryLayout.FindRoot());
        string[] configs = [RegManifestAgreement.LakefilePath, RegManifestAgreement.ManifestPath];
        var findings = FileMapPolicy.InspectPatternPopulation(manifest, configs.Where(path => path != missing));
        Assert.Equal(expected, findings.Count(finding =>
            finding.Path.StartsWith("Reg/", StringComparison.Ordinal) && finding.Path.EndsWith(".lean", StringComparison.Ordinal)));
    }

    [Theory]
    [InlineData("Reg/lakefile.toml")]
    [InlineData("Reg/lake-manifest.json")]
    public void EmptyRegFamiliesRejectUnregisteredPackageFiles(string unregistered)
    {
        var manifest = FileMapLoader.LoadRepository(TestRepositoryLayout.FindRoot());
        var incomplete = new FileMapManifest(manifest.ResidencePolicy,
            manifest.Entries.Where(entry => !entry.Matches(unregistered)).ToImmutableArray(), manifest.ArtifactKinds);
        var findings = FileMapPolicy.InspectPatternPopulation(incomplete,
            [RegManifestAgreement.LakefilePath, RegManifestAgreement.ManifestPath]);
        Assert.Equal(3, findings.Count(finding => finding.Path.StartsWith("Reg/", StringComparison.Ordinal)));
    }

    [Fact]
    public void PopulatedRegFamilyStillUsesItsTrackedSource()
    {
        var manifest = FileMapLoader.LoadRepository(TestRepositoryLayout.FindRoot());
        var findings = FileMapPolicy.InspectPatternPopulation(manifest, ["Reg/Support/Actual.lean"]);
        Assert.DoesNotContain(findings, finding => finding.Path == "Reg/Support/**/*.lean");
        Assert.Contains(findings, finding => finding.Path == "Reg/D5/**/*.lean");
    }

    [Theory]
    [InlineData("lean-build", "tools/scripts/worktree/lean-cache-run.sh")]
    [InlineData("lean-inspector", "tools/lean-inspector/inspect.sh")]
    public void RegLeanVerifiersRequireTheirRegisteredImplementation(string verifier, string implementation)
    {
        var manifest = FileMapLoader.LoadRepository(TestRepositoryLayout.FindRoot());
        Assert.Contains(verifier, FileMapPolicy.AvailableDataVerifiers(manifest,
            new HashSet<string>(StringComparer.Ordinal) { implementation }));
        Assert.DoesNotContain(verifier, FileMapPolicy.AvailableDataVerifiers(manifest,
            new HashSet<string>(StringComparer.Ordinal)));
        var dataOnly = FileMapLoader.Parse(System.Text.Encoding.UTF8.GetBytes($$"""
            schema_version = 6
            evidence = { artifact_kinds = { json = { profile = "structured-json", selectors = ["result"], path_selectors = ["formal"] } } }
            [residence_policy]
            case_id = "REG-VERIFIER-FIXTURE"
            desired = "registered"
            known_violation_count = 0
            status = "closed"
            [[files]]
            pattern = "Reg/D5/**/*.lean"
            kind = "data"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["Lean"]
            verified_by = ["{{verifier}}"]
            runtime_disposition = "committed-source"
            artifact_id = "none"
            """ + "\n"), "fixture.toml");
        Assert.DoesNotContain(verifier, FileMapPolicy.AvailableDataVerifiers(dataOnly,
            new HashSet<string>(StringComparer.Ordinal) { implementation }));
    }

    [Theory]
    [InlineData("SL-015", "Reg/lake-manifest.json", false)]
    [InlineData("SL-015", "Reg/lakefile.toml", false)]
    [InlineData("SL-003", "Reg/Support/X.lean", false)]
    [InlineData("SL-003", "Reg/lake-manifest.json", false)]
    public void RegChangesParticipateInCurrentCheckMaterials(string rule, string path, bool report)
    {
        using var json = JsonDocument.Parse(File.ReadAllBytes(
            Path.Combine(TestRepositoryLayout.FindRoot(), "Meta/ci-checks.json")));
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
        var entry = Assert.Single(FileMapLoader.LoadRepository(TestRepositoryLayout.FindRoot()).Match(path));
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
