using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RegisteredImpactTests
{
    private const string Configuration = "unusual/config/compiler.settings";
    private const string Neighbor = "tools/Directory.Build.props";
    private const string Producer = "Meta/ReportProducers/scribe-content.json";

    [Fact]
    public void RegisteredPolicyReaderChangesInvalidateRuleCatalog()
    {
        const string reader = "tools/StrataLint.Engine/RepositoryIo/EngineeringProjectRegistry.cs";
        var fixture = RegisteredFixture();
        var policy = JsonNode.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(),
            EngineeringRegistrationFixture.Path)))!["rule_build_inputs"]!;
        var manifest = JsonNode.Parse(fixture.Files[EngineeringRegistrationFixture.Path])!;
        manifest["rule_build_inputs"] = policy.DeepClone();
        fixture.Files[EngineeringRegistrationFixture.Path] = manifest.ToJsonString();
        foreach (var input in policy.AsArray()) fixture.Files.TryAdd(input!.GetValue<string>(), "registered input");
        fixture.Files[reader] = "// changed selection policy reader";
        Assert.True(fixture.Build(RawChangeSet.Create([reader])).RuleImplementationChanged);
    }

    [Theory]
    [InlineData(Configuration, true)]
    [InlineData(Neighbor, false)]
    [InlineData("tools/StrataLint.Engine/Rules/FutureRule.cs", true)]
    [InlineData("tools/StrataLint.Engine/UnrelatedHelper.cs", false)]
    public void RuleImpactUsesRegisteredConfigurationAndRetainsRuleSourceScope(string path, bool expected)
    {
        var fixture = RegisteredFixture();
        Assert.Equal(expected, fixture.Build(RawChangeSet.Create([path])).RuleImplementationChanged);
    }

    [Theory]
    [InlineData("missing-manifest")]
    [InlineData("missing-field")]
    [InlineData("duplicate-input")]
    [InlineData("missing-input")]
    public void InvalidRuleInputRegistrationFailsExplicitly(string defect)
    {
        var fixture = RegisteredFixture();
        if (defect == "missing-manifest") fixture.Files.Remove(EngineeringRegistrationFixture.Path);
        else if (defect == "missing-input") fixture.Files.Remove(Configuration);
        else
        {
            var manifest = JsonNode.Parse(fixture.Files[EngineeringRegistrationFixture.Path])!;
            if (defect == "missing-field") manifest.AsObject().Remove("rule_build_inputs");
            else manifest["rule_build_inputs"]!.AsArray().Add(Configuration);
            fixture.Files[EngineeringRegistrationFixture.Path] = manifest.ToJsonString();
        }
        var error = Assert.Throws<InvalidDataException>(() => fixture.Build(RawChangeSet.Create([Neighbor])));
        Assert.Contains("registration", error.Message);
    }

    [Theory]
    [InlineData(Configuration, true)]
    [InlineData(Neighbor, false)]
    [InlineData("tools/StrataLint.Engine/UnrelatedHelper.cs", true)]
    [InlineData("remote/library/Code.cs", true)]
    [InlineData("notes/unrelated.txt", false)]
    public void ScribeVerifierSelectsRegisteredProducerInputsAndStillChecksProjection(string changed, bool selected)
    {
        var fixture = RegisteredFixture();
        // The real projection reader must reject this payload whenever selected.
        fixture.Files["Golden/Projection/statement-projection-pilot-v1.json"] = "invalid projection";
        var verifier = new ProductionScribeEmissionVerifier((_, _, _, _) => VerifiedScribeEmissions.Empty);
        var snapshot = Snapshot(fixture);
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());
        if (selected) Assert.ThrowsAny<System.Text.Json.JsonException>(() => verifier.Verify(snapshot, report, RawChangeSet.Create([changed])));
        else Assert.Same(VerifiedScribeEmissions.Empty, verifier.Verify(snapshot, report, RawChangeSet.Create([changed])));
    }

    [Theory]
    [InlineData("missing-manifest")]
    [InlineData("duplicate-input")]
    [InlineData("missing-input")]
    [InlineData("unregistered-project")]
    [InlineData("missing-compile")]
    [InlineData("unregistered-reference")]
    [InlineData("conflicting-assembly")]
    public void InvalidScribeInputRegistrationFailsExplicitly(string defect)
    {
        var fixture = RegisteredFixture();
        if (defect == "missing-manifest") fixture.Files.Remove(Producer);
        else if (defect == "missing-input") fixture.Files.Remove(Configuration);
        else if (defect is "missing-compile" or "unregistered-reference" or "conflicting-assembly")
        {
            var manifest = JsonNode.Parse(fixture.Files[EngineeringRegistrationFixture.Path])!;
            var row = manifest["projects"]!.AsArray().Single(row =>
                row!["path"]!.GetValue<string>() == "tools/StrataLint.Scribe/StrataLint.Scribe.csproj")!;
            if (defect == "missing-compile") row["include"] = new JsonArray("unusual/Missing.cs");
            else if (defect == "unregistered-reference") row["references"] = new JsonArray("missing/Library.csproj");
            else row["assembly"] = "Registered.Library";
            fixture.Files[EngineeringRegistrationFixture.Path] = manifest.ToJsonString();
        }
        else
        {
            var manifest = JsonNode.Parse(fixture.Files[Producer])!;
            if (defect == "duplicate-input") manifest["materials"]!.AsArray().Add(Configuration);
            else manifest["projects"]!.AsArray().Add("absent/Unregistered.csproj");
            fixture.Files[Producer] = manifest.ToJsonString();
        }
        var verifier = new ProductionScribeEmissionVerifier((_, _, _, _) => VerifiedScribeEmissions.Empty);
        var error = Assert.Throws<InvalidDataException>(() => verifier.Verify(Snapshot(fixture),
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()), RawChangeSet.Create(["notes/unrelated.txt"])));
        Assert.Contains("registration", error.Message);
    }

    private static RuleFixture RegisteredFixture()
    {
        var fixture = new RuleFixture();
        const string library = "remote/library/Explicit.csproj";
        fixture.Files[EngineeringRegistrationFixture.Path] = EngineeringRegistrationFixture.Append(
            fixture.Files[EngineeringRegistrationFixture.Path], new EngineeringProjectFixture(
                library, "Registered.Library", "test-support", false, ["remote/library/**/*.cs"]));
        fixture.Files[library] = "<Project />";
        fixture.Files["remote/library/Code.cs"] = "namespace Fixture; class Library { }";
        var manifest = JsonNode.Parse(fixture.Files[EngineeringRegistrationFixture.Path])!;
        manifest["projects"]![0]!["references"] = new JsonArray(library);
        manifest["rule_build_inputs"] = new JsonArray(Configuration);
        fixture.Files[EngineeringRegistrationFixture.Path] = manifest.ToJsonString();
        fixture.Files[Configuration] = "declared compiler input";
        fixture.Files[Neighbor] = "unregistered same-basename neighbor";
        fixture.Files[Producer] = """
            {"schema":"report-producer-scope-v1","scripts":[],
             "projects":["tools/StrataLint.Scribe/StrataLint.Scribe.csproj"],
             "materials":["unusual/config/compiler.settings"]}
            """;
        return fixture;
    }

    private static RepositorySnapshot Snapshot(RuleFixture fixture) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            fixture.Files.Select(file => RawRepositoryEntry.FromText(file.Key, file.Value))))).Snapshot;
}
