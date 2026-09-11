using StrataLint.TestSupport;

namespace StrataLint.ArchitectureTests;

public sealed class EngineeringProjectRegistrationTests
{
    private const string Project = "odd/LooksLikeProduction.csproj";
    private const string Misleading = "<Project><PropertyGroup><AssemblyName>Wrong</AssemblyName><IsTestProject>false</IsTestProject></PropertyGroup></Project>";

    [Fact]
    public void ExplicitClassificationWinsOverNameLocationAndMetadata()
    {
        var snapshot = Snapshot(EngineeringRegistrationFixture.Manifest(Test()), (Project, Misleading));
        Assert.Equal([Project], EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(snapshot)).ToArray());
    }

    [Fact]
    public void UnregisteredXunitProjectFailsInsteadOfBeingDiscovered()
    {
        var snapshot = Snapshot(EngineeringRegistrationFixture.Manifest(),
            (Project, "<Project><ItemGroup><PackageReference Include=\"xunit\" /></ItemGroup></Project>"));
        Assert.Throws<InvalidDataException>(() => RepositoryRules.ReadSnapshotProjects(snapshot));
    }

    [Fact]
    public void MissingManifestFailsEvenForAnEmptyTree() =>
        Assert.Throws<InvalidDataException>(() => RepositoryRules.ReadSnapshotProjects(Snapshot(null)));

    [Fact]
    public void DuplicateProjectRegistrationFails() =>
        Assert.Throws<InvalidDataException>(() => RepositoryRules.ReadSnapshotProjects(
            Snapshot(EngineeringRegistrationFixture.Manifest(Test(), Test()), (Project, Misleading))));

    [Fact]
    public void MissingRegisteredProjectFails() =>
        Assert.Throws<InvalidDataException>(() => RepositoryRules.ReadSnapshotProjects(
            Snapshot(EngineeringRegistrationFixture.Manifest(Test()))));

    [Theory]
    [InlineData("{\"version\":1,\"version\":1,\"projects\":[],\"historical_projects\":[]}")]
    [InlineData("{\"version\":1,\"projects\":[],\"historical_projects\":[],\"discovery\":true}")]
    [InlineData("{\"version\":1,\"projects\":[]}")]
    public void MalformedRegistrationFails(string manifest) =>
        Assert.Throws<InvalidDataException>(() => RepositoryRules.ReadSnapshotProjects(Snapshot(manifest)));

    [Fact]
    public void SupportAndProofRolesDoNotBecomeTestsFromXunitMetadata()
    {
        var entries = new[] { Test() with { Role = "test-support", Ci = false },
            Test() with { Path = "proof/p.csproj", Role = "compile-fail-proof", Ci = false } };
        var snapshot = Snapshot(EngineeringRegistrationFixture.Manifest(entries),
            entries.Select(entry => (entry.Path, "<Project><ItemGroup><PackageReference Include=\"xunit\" /></ItemGroup></Project>")).ToArray());
        Assert.Empty(EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(snapshot)).ToArray());
        Assert.Empty(RepositoryRules.CalculateDebt(RepositoryRules.ReadSnapshotProjects(snapshot)));
    }

    [Fact]
    public void BasePredatingRegistryUsesCandidateDeclarationsAndStillHasAnExecutionFloor()
    {
        var baseline = Snapshot(null, (Project, Misleading));
        var candidate = Snapshot(EngineeringRegistrationFixture.Manifest(Test()), (Project, Misleading));
        Assert.Equal([Project], EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadBaseProjects(baseline, candidate)).ToArray());
        Assert.False(baseline.TryGetFile(EngineeringRegistrationFixture.Path, out _));
    }

    // Original version-1 row from 653216143592d41af04f03074f33d07668d8d257.
    // Deliberately independent of the candidate fixture writer and its namespace policy.
    private const string PriorRegistration = """
        {"version":1,"projects":[{
          "path":"tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
          "assembly":"StrataLint.ArchitectureTests","role":"cross-cutting-test","ci":true,
          "include":["tools/tests/StrataLint.ArchitectureTests/**/*.cs"],"exclude":[],
          "references":["tools/StrataLint.Engine/StrataLint.Engine.csproj",
            "tools/StrataLint.Cli/StrataLint.Cli.csproj","tools/StrataLint.Scribe/StrataLint.Scribe.csproj",
            "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj",
            "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj",
            "tools/TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj"],
          "owner":null,"owned_test_assembly":null,"test_partition":"tools/tests/StrataLint.ArchitectureTests"
        }],"historical_projects":[]}
        """;

    [Fact]
    public void OriginalTenFieldBaseRegistrationRetainsRemovedProjectInExecutionFloor()
    {
        const string path = "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj";
        var baseline = Snapshot(PriorRegistration, (path, Misleading));
        var candidate = Snapshot(EngineeringRegistrationFixture.Manifest());
        Assert.Equal([path], EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadBaseProjects(baseline, candidate)).ToArray());
        Assert.Empty(EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(candidate)));
    }

    [Fact]
    public void BaseDeclarationReadIgnoresPolicyItDoesNotConsume()
    {
        const string path = "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj";
        var manifest = System.Text.Json.Nodes.JsonNode.Parse(PriorRegistration)!;
        manifest["projects"]![0]!["execution_inputs"] = new System.Text.Json.Nodes.JsonArray("not-consumed");
        var baseline = Snapshot(manifest.ToJsonString(), (path, Misleading));
        Assert.Equal([path], EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadBaseProjects(baseline,
            Snapshot(EngineeringRegistrationFixture.Manifest()))).ToArray());
    }

    [Theory]
    [InlineData("path")]
    [InlineData("assembly")]
    [InlineData("role")]
    [InlineData("ci")]
    [InlineData("references")]
    [InlineData("owner")]
    [InlineData("owned_test_assembly")]
    [InlineData("test_partition")]
    public void BaseDeclarationReadRequiresEveryConsumedField(string field)
    {
        var manifest = System.Text.Json.Nodes.JsonNode.Parse(PriorRegistration)!;
        manifest["projects"]![0]!.AsObject().Remove(field);
        var error = Assert.Throws<InvalidDataException>(() => RepositoryRules.ReadBaseProjects(
            Snapshot(manifest.ToJsonString()), Snapshot(EngineeringRegistrationFixture.Manifest())));
        Assert.Contains(field, error.Message);
    }

    [Fact]
    public void HistoricalProjectionDoesNotRelaxCandidateRegistration()
    {
        var error = Assert.Throws<InvalidDataException>(() => RepositoryRules.ReadSnapshotProjects(Snapshot(PriorRegistration)));
        Assert.Contains("root_namespace", error.Message);
    }

    [Fact]
    public void HistoricalProjectCannotDisappearFromBaseExecutionFloor()
    {
        var baseline = Snapshot(null, (Project, Misleading));
        var manifest = System.Text.Json.Nodes.JsonNode.Parse(EngineeringRegistrationFixture.Manifest(Test()))!;
        manifest["historical_projects"] = manifest["projects"]!.DeepClone();
        manifest["projects"] = new System.Text.Json.Nodes.JsonArray();
        var candidate = Snapshot(manifest.ToJsonString());
        Assert.Empty(EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(candidate)));
        Assert.Equal([Project], EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadBaseProjects(baseline, candidate)).ToArray());
        Assert.Throws<InvalidDataException>(() => RepositoryRules.ReadBaseProjects(baseline,
            Snapshot(EngineeringRegistrationFixture.Manifest())));
    }

    [Fact]
    public void ExplicitOwnerRelationDoesNotRequireMatchingProjectOrAssemblyNames()
    {
        const string production = "somewhere/Unexpected.Tests.csproj";
        var manifest = EngineeringRegistrationFixture.Manifest(
            new EngineeringProjectFixture(production, "Unrelated.Library", "production", false, [], OwnedTestAssembly: "Explicit.Checks"),
            Test() with { Role = "owned-test", Owner = new(production, "Unrelated.Library"), References = [production] });
        var snapshot = Snapshot(manifest, (production, Misleading), (Project, Misleading));
        Assert.Empty(RepositoryRules.CalculateDebt(RepositoryRules.ReadSnapshotProjects(snapshot)));
    }

    [Fact]
    public void RepositoryRegistrationKeepsScriptCiExclusionAndBothProofProjects()
    {
        var topology = RepositoryRules.ReadTrackedProjects(RepositoryLayout.FindRoot());
        const string scripts = "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";
        Assert.Equal("cross-cutting-test", Assert.Single(topology.Projects, project => project.Path == scripts).Registration.Role);
        Assert.DoesNotContain(scripts, EngineeringTestPlanPolicy.Evaluate(topology));
        Assert.Equal(new[]
        {
            "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj",
            "tools/tests/CompileFailProof/CompileFailProof.csproj",
        }, topology.Projects.Where(project => project.Registration.Role == "compile-fail-proof").Select(project => project.Path));
    }


    [Theory]
    [InlineData("root_namespace")]
    [InlineData("namespace_exclude")]
    [InlineData("global_namespace_exceptions")]
    public void MissingNamespacePolicyFieldFails(string field)
    {
        var manifest = System.Text.Json.Nodes.JsonNode.Parse(EngineeringRegistrationFixture.Manifest(Test()))!;
        manifest["projects"]![0]!.AsObject().Remove(field);
        var error = Assert.Throws<InvalidDataException>(() => EngineeringProjectRegistry.Read(
            Snapshot(manifest.ToJsonString(), (Project, Misleading))));
        Assert.Contains(field, error.Message);
    }

    [Theory]
    [InlineData("root_namespace", "null")]
    [InlineData("root_namespace", "\"\"")]
    [InlineData("root_namespace", "\"A..B\"")]
    [InlineData("root_namespace", "\"A B\"")]
    [InlineData("root_namespace", "\" A.B\"")]
    [InlineData("root_namespace", "\"A.B;\"")]
    [InlineData("namespace_exclude", "null")]
    [InlineData("namespace_exclude", "[\"../Escape.cs\"]")]
    [InlineData("namespace_exclude", "[\"tools/A.cs\",\"tools/A.cs\"]")]
    [InlineData("global_namespace_exceptions", "null")]
    [InlineData("global_namespace_exceptions", "[\"tools/**/*.cs\"]")]
    [InlineData("global_namespace_exceptions", "[\"tools/A.cs\",\"tools/A.cs\"]")]
    [InlineData("global_namespace_exceptions", "[\"../A.cs\"]")]
    [InlineData("global_namespace_exceptions", "[\"tools/A.txt\"]")]
    public void MalformedNamespacePolicyFieldFails(string field, string value)
    {
        var manifest = System.Text.Json.Nodes.JsonNode.Parse(EngineeringRegistrationFixture.Manifest(Test()))!;
        manifest["projects"]![0]![field] = System.Text.Json.Nodes.JsonNode.Parse(value);
        Assert.Throws<InvalidDataException>(() => EngineeringProjectRegistry.Read(
            Snapshot(manifest.ToJsonString(), (Project, Misleading))));
    }

    private static EngineeringProjectFixture Test() => new(Project, "Explicit.Checks", "cross-cutting-test", true, []);

    internal static RepositorySnapshot Snapshot(string? manifest, params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            files.Select(file => RawRepositoryEntry.FromText(file.Path, file.Text)).Concat(manifest is null ? [] :
                new[] { RawRepositoryEntry.FromText(EngineeringRegistrationFixture.Path, manifest) })))).Snapshot;
}
