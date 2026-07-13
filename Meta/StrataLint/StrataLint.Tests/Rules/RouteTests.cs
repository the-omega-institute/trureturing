using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RouteTests
{
    [Theory]
    [InlineData("F", "Carrier", "Probe", "", "lean", "", "D5/S0/Carrier/Probe", "D5/S0/Carrier/Probe.lean")]
    [InlineData("B", "Carrier", "Probe", "", "markdown", "", "D5/B/S0/Carrier/Probe", "Blueprint/D5/S0/Carrier/Probe.md")]
    [InlineData("E", "Carrier", "Probe", "result", "json", "", "D5/E/S0/Carrier/Probe.result--json", "Evidence/D5/S0/Carrier/Probe.result.json")]
    [InlineData("E", "values", "values", "result", "json", "", "D5/E/values--json", "Evidence/D5/values.json")]
    [InlineData("C", "2026-07-11", "round-168", "", "markdown", "", "D5/C/2026-07-11/round-168", "Chronicle/2026/07/11-round-168.md")]
    [InlineData("L", "Notes", "sample2026paper", "", "markdown", "", "D5/L/sample2026paper", "Library/notes/sample2026paper.md")]
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
        var manifest = new ManifestSyntax("D5", plane, domain, module, "G", selector, artifact, tag);

        var outcome = RouteEngine.Route(policy, manifest);

        var routed = Assert.IsType<RouteOutcome.Routed>(outcome);
        Assert.Equal(expectedGid, routed.Result.Gid.Value);
        Assert.Equal(expectedPath, routed.Result.Path.Value);
        Assert.Empty(typeof(ValidatedManifest).GetConstructors());
    }

    [Fact]
    public void RouteRejectsUninstantiatedTheoryAndDanglingArtifactReference()
    {
        var policy = Policy();

        var future = RouteEngine.Route(
            policy,
            new ManifestSyntax("D8", "F", "Carrier", "Probe", "G", "", "lean", ""));
        var unknownArtifact = RouteEngine.Route(
            policy,
            new ManifestSyntax("D5", "E", "Carrier", "Probe", "G", "result", "toml", ""));

        Assert.Equal(RuleId.CreateKnown(21), Assert.IsType<RouteOutcome.Rejected>(future).RuleId);
        Assert.Equal(RuleId.CreateKnown(15), Assert.IsType<RouteOutcome.Rejected>(unknownArtifact).RuleId);
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
        Assert.IsType<RegistryLoadOutcome.Accepted>(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
}
