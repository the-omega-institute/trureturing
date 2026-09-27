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
    public void ScopedRemovalOfLastRegSourceKeepsPackageContext()
    {
        using var repository = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        foreach (var path in new[] { "Meta/FILEMAP.toml", "Meta/FILEMAP.docs.reports.toml",
                     "Meta/domains.yaml", ".gitignore",
                     RegManifestAgreement.LakefilePath, RegManifestAgreement.ManifestPath }
                     .Concat(FileMapLoader.LoadRepository(root).Resources.SelectMany(resource =>
                         resource.Materials.Prepend(resource.Owner))).Distinct(StringComparer.Ordinal))
        {
            var target = Path.Combine(repository.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(Path.Combine(root, path), target);
        }
        const string removed = "Reg/Support/Last.lean";
        var source = Path.Combine(repository.Path, removed);
        Directory.CreateDirectory(Path.GetDirectoryName(source)!);
        File.WriteAllText(source, "-- last declaration source\n");
        Git("init");
        Git("add", "--all");
        Git("rm", "--force", removed);
        var paths = GitIndexRepositoryFiles.Enumerate(repository.Path).Select(file => file.RelativePath).ToArray();
        using var checks = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "Meta/ci-checks.json")));
        var registration = checks.RootElement.GetProperty("checks").EnumerateArray()
            .Single(row => row.GetProperty("id").GetString() == "filemap")
            .GetProperty("delta_scope").Deserialize<RegisteredFileMapScope>(new JsonSerializerOptions
                { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower });
        var scope = FileMapInspectionScope.Select(registration, [removed], paths);
        Assert.Equal(new[] { removed }, scope.Paths);
        var population = FileMapPolicy.InspectRepository(repository.Path,
                DocumentAssembly.Definitions.Select(definition => definition.RelativePath.Value), scope)
            .Where(finding => finding.Code == "FILEMAP-PATTERN-EMPTY").ToArray();
        Assert.Empty(population);

        void Git(params string[] arguments) => Assert.Equal(0, TestProcessRunner.Run(
            "git", arguments, repository.Path, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024).ExitCode);
    }

    [Theory]
    [InlineData("StrataLint.RepositoryFileMap.Tests", "execution_inputs")]
    [InlineData("StrataLint.RepositoryTopology.Tests", "execution_path_inventory")]
    public void RepositoryRegSourcesParticipateInTestInputs(string project, string inputField)
    {
        const string registrationPath = "Meta/engineering-projects.json";
        using var json = JsonDocument.Parse(File.ReadAllBytes(
            Path.Combine(TestRepositoryLayout.FindRoot(), registrationPath)));
        var registration = json.RootElement.GetProperty("projects").EnumerateArray()
            .Single(item => item.GetProperty("path").GetString() == $"tools/tests/{project}/{project}.csproj");
        Assert.Contains(registration.GetProperty(inputField).EnumerateArray(),
            item => FileMapGlob.Create(item.GetString()!).IsMatch("Reg/Support/X.lean"));
        if (inputField == "execution_path_inventory")
            Assert.DoesNotContain(registration.GetProperty("execution_inputs").EnumerateArray(),
                item => FileMapGlob.Create(item.GetString()!).IsMatch("Reg/Support/X.lean"));
    }

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
            manifest.Entries.Where(entry => !entry.Matches(unregistered)).ToImmutableArray(), manifest.ArtifactKinds, manifest.Resources);
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
            schema_version = 5
            resources = []
            evidence = { artifact_kinds = { json = { profile = "structured-json", selectors = ["result"], path_selectors = ["formal"] } } }
            [residence_policy]
            case_id = "REG-VERIFIER-FIXTURE"
            desired = "registered"
            known_violation_count = 0
            status = "closed"
            [[files]]
            pattern = "Reg/D5/**/*.lean"
            require = []
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
    [InlineData("SL-002", "Reg/Support/X.lean", true)]
    [InlineData("SL-020", "Reg/D5/S3/Arith/X.lean", true)]
    [InlineData("SL-003", "Reg/Support/X.lean", false)]
    [InlineData("SL-003", "Reg/lake-manifest.json", false)]
    [InlineData("filemap", "Reg/Support/X.lean", false)]
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
