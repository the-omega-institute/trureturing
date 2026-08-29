using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RouteTests
{
    [Theory]
    [InlineData("F", "Carrier", "Probe", "", "lean", "", "D5/S0/Carrier/Probe", "D5/S0/Carrier/Probe.lean")]
    [InlineData("B", "Carrier", "Probe", "", "markdown", "", "D5/B/S0/Carrier/Probe", "Blueprint/D5/S0/Carrier/Probe.md")]
    [InlineData("E", "Carrier", "Probe", "result", "json", "", "D5/E/S0/Carrier/Probe.result--json", "Evidence/D5/S0/Carrier/Probe.result.json")]
    [InlineData("E", "values", "values", "result", "json", "", "D5/E/values--json", RuleFixture.ValuesProjectionPath)]
    [InlineData("C", "2026-07-11", "round-168", "", "markdown", "", "D5/C/2026-07-11/round-168", "Chronicle/2026/07/11-round-168.md")]
    [InlineData("L", "Notes", "sample2026paper", "", "markdown", "", "D5/L/sample2026paper", "Library/notes/sample2026paper.md")]
    [InlineData("L", "Weil", "sample2026paper", "", "markdown", "", "D5/L/Weil/sample2026paper", "Library/Weil/sample2026paper.md")]
    [InlineData("P", "Papers", "D5-P001", "", "frozen", "frozen", "D5/P/D5-P001--frozen", "Papers/frozen/D5-P001/manifest.sha256")]
    public void RouteCoversAllPlanesThroughCanonicalGidCodec(
        string plane,
        string domain,
        string module,
        string selector,
        string artifact,
        string tag,
        string expectedGid,
        string expectedPath)
    {
        var policy = Policy();
        var manifest = new ManifestSyntax("D5", plane, domain, module, "G", selector, artifact, tag, null);

        var outcome = RouteEngine.Route(policy, manifest);

        var routed = Assert.IsType<RouteOutcome.Routed>(outcome);
        Assert.Equal(expectedGid, routed.Result.Gid.Value);
        Assert.Equal(expectedPath, routed.Result.Path.Value);
        Assert.Empty(typeof(ValidatedManifest).GetConstructors());
    }

    [Theory]
    [InlineData("F", "lean", "", "D5/S0/Carrier/Algebra/Probe", "D5/S0/Carrier/Algebra/Probe.lean")]
    [InlineData("B", "markdown", "", "D5/B/S0/Carrier/Algebra/Probe", "Blueprint/D5/S0/Carrier/Algebra/Probe.md")]
    [InlineData("E", "json", "result", "D5/E/S0/Carrier/Algebra/Probe.result--json", "Evidence/D5/S0/Carrier/Algebra/Probe.result.json")]
    public void RouteWithSubDomainProducesFourCoordinateArtifactPaths(
        string plane,
        string artifact,
        string selector,
        string expectedGid,
        string expectedPath)
    {
        var manifest = new ManifestSyntax(
            "D5", plane, "Carrier", "Probe", "G", selector, artifact, "", SubDomain: "Algebra");

        var routed = Assert.IsType<RouteOutcome.Routed>(RouteEngine.Route(Policy(), manifest));

        Assert.Equal(expectedGid, routed.Result.Gid.Value);
        Assert.Equal(expectedPath, routed.Result.Path.Value);
    }

    [Theory]
    [InlineData("algebra", "subdomain must be CamelCase")]
    [InlineData("Carrier", "subdomain must differ from domain")]
    [InlineData("", "subdomain must not be empty")]
    public void RouteRejectsInvalidSubDomainAtTheCoordinateAssertion(string subDomain, string expectedMessage)
    {
        var manifest = new ManifestSyntax(
            "D5", "F", "Carrier", "Probe", "G", "", "lean", "", SubDomain: subDomain);

        var rejected = Assert.IsType<RouteOutcome.Rejected>(RouteEngine.Route(Policy(), manifest));

        Assert.Equal(RuleId.CreateKnown(15), rejected.RuleId);
        Assert.Equal(expectedMessage, rejected.Message);
    }

    [Theory]
    [InlineData("X_Assumptions")]
    [InlineData("X_Certificates")]
    [InlineData("X_Frontier")]
    public void SpecialZoneRouteRejectsSubDomainAtItsOwningAssertion(string specialZone)
    {
        var manifest = new ManifestSyntax(
            "D5", "F", specialZone, "Probe", "G", "", "lean", "", SubDomain: "Algebra");

        var rejected = Assert.IsType<RouteOutcome.Rejected>(RouteEngine.Route(Policy(), manifest));

        Assert.Equal(RuleId.CreateKnown(15), rejected.RuleId);
        Assert.Equal("special-zone route cannot have a subdomain", rejected.Message);
    }

    [Theory]
    [InlineData("C", "2026-07-11", "round-168", "", "markdown", "")]
    [InlineData("L", "Notes", "sample2026paper", "", "markdown", "")]
    [InlineData("P", "Papers", "D5-P001", "", "recipe", "")]
    [InlineData("E", "values", "values", "result", "json", "")]
    public void RouteRejectsSubDomainForNonFormalManifestShapes(
        string plane,
        string domain,
        string module,
        string selector,
        string artifact,
        string tag)
    {
        var manifest = new ManifestSyntax(
            "D5", plane, domain, module, "G", selector, artifact, tag, SubDomain: "Algebra");

        var rejected = Assert.IsType<RouteOutcome.Rejected>(RouteEngine.Route(Policy(), manifest));

        Assert.Equal(RuleId.CreateKnown(15), rejected.RuleId);
        Assert.Equal("subdomain is only allowed for F, B, or formal E manifests", rejected.Message);
    }

    [Theory]
    [InlineData(false, null)]
    [InlineData(true, "Algebra")]
    public void ManifestLoaderAcceptsOptionalSubdomainWithoutWeakeningStrictKeys(bool includeSubdomain, string? expected)
    {
        var subdomain = includeSubdomain ? ",\"subdomain\":\"Algebra\"" : string.Empty;
        var json = "{\"artifact\":\"lean\",\"domain\":\"Carrier\",\"generality\":\"G\",\"module\":\"Probe\",\"plane\":\"F\",\"selector\":\"\",\"tag\":\"\",\"theory\":\"D5\"" + subdomain + "}";

        var loaded = Assert.IsType<ManifestLoadOutcome.Loaded>(ManifestLoader.Load(Encoding.UTF8.GetBytes(json)));

        Assert.Equal(expected, loaded.Syntax.SubDomain);
        Assert.Equal(
            includeSubdomain ? "D5/S0/Carrier/Algebra/Probe" : "D5/S0/Carrier/Probe",
            Assert.IsType<RouteOutcome.Routed>(RouteEngine.Route(Policy(), loaded.Syntax)).Result.Gid.Value);
    }

    [Fact]
    public void ManifestLoaderAcceptsOptionalSubdomainFromYamlAndRoutesIt()
    {
        const string yaml = """
            artifact: lean
            domain: Carrier
            generality: G
            module: Probe
            plane: F
            selector: ''
            subdomain: Algebra
            tag: ''
            theory: D5
            """;

        var loaded = Assert.IsType<ManifestLoadOutcome.Loaded>(
            ManifestLoader.Load(Encoding.UTF8.GetBytes(yaml)));

        Assert.Equal("Algebra", loaded.Syntax.SubDomain);
        Assert.Equal(
            "D5/S0/Carrier/Algebra/Probe",
            Assert.IsType<RouteOutcome.Routed>(RouteEngine.Route(Policy(), loaded.Syntax)).Result.Gid.Value);
    }

    [Theory]
    [InlineData("json", "{\"artifact\":\"lean\",\"domain\":\"Carrier\",\"generality\":\"G\",\"module\":\"Probe\",\"plane\":\"F\",\"selector\":\"\",\"subdomain\":\"\",\"tag\":\"\",\"theory\":\"D5\"}")]
    [InlineData("yaml", "artifact: lean\ndomain: Carrier\ngenerality: G\nmodule: Probe\nplane: F\nselector: ''\nsubdomain: ''\ntag: ''\ntheory: D5\n")]
    public void ManifestLoaderRejectsPresentButEmptySubdomain(string _, string manifest)
    {
        var failure = Assert.IsType<ManifestLoadOutcome.InfrastructureFailure>(
            ManifestLoader.Load(Encoding.UTF8.GetBytes(manifest)));

        Assert.Equal("subdomain must not be empty", failure.Message);
    }

    [Theory]
    [InlineData("C", "2026-07-11", "round-168", "", "markdown", "")]
    [InlineData("L", "Notes", "sample2026paper", "", "markdown", "")]
    [InlineData("P", "Papers", "D5-P001", "", "recipe", "")]
    [InlineData("E", "values", "values", "result", "json", "")]
    public void ManifestLoaderRejectsSubdomainForNonFormalManifestShapes(
        string plane,
        string domain,
        string module,
        string selector,
        string artifact,
        string tag)
    {
        var json = JsonSerializer.Serialize(new
        {
            artifact,
            domain,
            generality = "G",
            module,
            plane,
            selector,
            subdomain = "Algebra",
            tag,
            theory = "D5",
        });

        var failure = Assert.IsType<ManifestLoadOutcome.InfrastructureFailure>(
            ManifestLoader.Load(Encoding.UTF8.GetBytes(json)));

        Assert.Equal("subdomain is only allowed for F, B, or formal E manifests", failure.Message);
    }

    [Fact]
    public void RouteRejectsUninstantiatedTheoryAndDanglingArtifactReference()
    {
        var policy = Policy();

        var future = RouteEngine.Route(
            policy,
            new ManifestSyntax("D8", "F", "Carrier", "Probe", "G", "", "lean", "", null));
        var unknownArtifact = RouteEngine.Route(
            policy,
            new ManifestSyntax("D5", "E", "Carrier", "Probe", "G", "result", "toml", "", null));

        Assert.Equal(RuleId.CreateKnown(21), Assert.IsType<RouteOutcome.Rejected>(future).RuleId);
        Assert.Equal(RuleId.CreateKnown(15), Assert.IsType<RouteOutcome.Rejected>(unknownArtifact).RuleId);
    }

    [Fact]
    public void RouteRejectsLibrarySplitBucketOutsideControlledDomains()
    {
        var outcome = RouteEngine.Route(
            Policy(),
            new ManifestSyntax(
                "D5",
                "L",
                "Unknown",
                "sample2026paper",
                "G",
                "",
                "markdown",
                "",
                null));

        Assert.Equal(RuleId.CreateKnown(15), Assert.IsType<RouteOutcome.Rejected>(outcome).RuleId);
    }

    [Fact]
    public void ManifestLoaderRejectsUnknownOrMissingKeys()
    {
        const string json = """
            {"artifact":"lean","domain":"Carrier","generality":"G","module":"Probe","plane":"F","selector":"","tag":"","theory":"D5","extra":"forbidden"}
            """;

        var outcome = ManifestLoader.Load(Encoding.UTF8.GetBytes(json));

        var failure = Assert.IsType<ManifestLoadOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("keys", failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    private static ValidatedPolicy Policy() =>
        RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
}
