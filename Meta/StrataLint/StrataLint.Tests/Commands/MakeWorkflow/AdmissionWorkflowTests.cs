using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed class AdmissionWorkflowTests
{
    [Fact]
    public void ReconcilesStatementProjectionAfterProducingLiveReport()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var leanInspect = Assert.IsType<YamlMappingNode>(jobs.Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(leanInspect.Children[new YamlScalarNode("steps")]);
        var namedSteps = steps.Children.OfType<YamlMappingNode>()
            .Select(static step => new
            {
                Node = step,
                Name = Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("name")]).Value,
            })
            .ToArray();
        var reportIndex = Array.FindIndex(namedSteps, static step =>
            step.Name == "Produce source-bound canonical Lean reports");
        var reconciliationIndex = Array.FindIndex(namedSteps, static step =>
            step.Name == "Reconcile pinned statement projections with live Lean report");
        Assert.True(reportIndex >= 0, "admission must produce the canonical live Lean report");
        Assert.True(reconciliationIndex > reportIndex, "reconciliation must run after report production");

        var reconciliation = namedSteps[reconciliationIndex].Node;
        var environment = Assert.IsType<YamlMappingNode>(reconciliation.Children[new YamlScalarNode("env")]);
        Assert.Equal("1", Assert.IsType<YamlScalarNode>(
            environment.Children[new YamlScalarNode("STRATALINT_REQUIRE_LIVE_REPORT")]).Value);
        var run = Assert.IsType<YamlScalarNode>(reconciliation.Children[new YamlScalarNode("run")]).Value!;
        Assert.Contains(
            "FullyQualifiedName=StrataLint.Scribe.Tests.StatementProjectionPilotTests.LiveReportMatchesPinnedFixtureWhenAvailable",
            run,
            StringComparison.Ordinal);
        Assert.Contains(
            "FullyQualifiedName=StrataLint.Scribe.Tests.DocumentDiscoveryTests.GeneratedMarkdownIsDeterministicAndMatchesTheCommittedTree",
            run,
            StringComparison.Ordinal);
        Assert.Contains("--logger \"trx;LogFileName=$results\"", run, StringComparison.Ordinal);
        Assert.Contains("len(results) != 2", run, StringComparison.Ordinal);
        Assert.Contains("set(names) != expected", run, StringComparison.Ordinal);
    }

    private static string FindRepositoryRoot()
    {
        for (var directory = new DirectoryInfo(AppContext.BaseDirectory);
             directory is not null;
             directory = directory.Parent)
        {
            if (File.Exists(Path.Combine(directory.FullName, "lakefile.toml")))
                return directory.FullName;
        }

        throw new InvalidOperationException("Repository root was not found.");
    }
}
