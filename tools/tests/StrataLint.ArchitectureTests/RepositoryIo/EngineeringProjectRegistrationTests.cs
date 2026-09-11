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

    private static EngineeringProjectFixture Test() => new(Project, "Explicit.Checks", "cross-cutting-test", true, []);

    internal static RepositorySnapshot Snapshot(string? manifest, params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            files.Select(file => RawRepositoryEntry.FromText(file.Path, file.Text)).Concat(manifest is null ? [] :
                new[] { RawRepositoryEntry.FromText(EngineeringRegistrationFixture.Path, manifest) })))).Snapshot;
}
