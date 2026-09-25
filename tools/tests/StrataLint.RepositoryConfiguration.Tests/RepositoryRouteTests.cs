using StrataLint.Configuration;
using StrataLint.Engine;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.RepositoryConfiguration.Tests;

public sealed class RepositoryRouteTests
{
    [Theory]
    [InlineData("C", "2026-07-11", "round-168", "", "markdown", "", "D5/C/2026-07-11/round-168", "Chronicle/2026/07/11-round-168.md")]
    [InlineData("P", "Papers", "D5-P001", "", "recipe", "", "D5/P/D5-P001", "Papers/recipes/D5-P001.yaml")]
    [InlineData("P", "Papers", "D5-P001", "", "frozen", "frozen", "D5/P/D5-P001--frozen", "Papers/frozen/D5-P001/manifest.sha256")]
    public void RealRepositoryRoutesPreserveChronicleAndPaperContracts(
        string plane,
        string domain,
        string module,
        string selector,
        string artifact,
        string tag,
        string expectedGid,
        string expectedPath)
    {
        var manifest = new ManifestSyntax("D5", plane, domain, module, "G", selector, artifact, tag, null);
        var currentPolicy = PolicyLoadAssert.Accepted(
            RepositoryPolicyLoader.LoadRepository(TestRepositoryLayout.FindRoot())).Policy;
        var currentRouted = Assert.IsType<RouteOutcome.Routed>(
            RouteEngine.Route(currentPolicy, manifest)).Result;
        string[] skeleton = artifact switch
        {
            "markdown" => [$"<!-- GID: {expectedGid} -->", $"# {module}", "", "EDIT-ME"],
            "recipe" => ["id: D5-P001", "decls: []", "blueprint: []", "evidence: []", "venue: EDIT-ME"],
            _ => ["EDIT-ME  manifest.sha256"],
        };
        Assert.Equal(skeleton, currentRouted.Skeleton);
        Assert.True(RepositoryPathPolicy.TryResolve(currentRouted.Path, out var reverse));
        Assert.Equal(currentRouted.Gid, reverse);
        Assert.Empty(currentPolicy.Manifest.Match(expectedPath));
        Assert.Equal(
            RuleId.CreateKnown(0),
            RepositoryPathPolicy.Validate(currentRouted.Path, currentPolicy)!.RuleId);
        Assert.False(RepositoryPathPolicy.TryResolve(currentRouted.Path, currentPolicy, out _));
        Assert.IsType<RouteOutcome.Rejected>(
            RouteEngine.Route(currentPolicy, manifest with { Module = "../note" }));
        Assert.IsType<RouteOutcome.Rejected>(
            RouteEngine.Route(currentPolicy, manifest with { Selector = "unexpected" }));
    }
}
