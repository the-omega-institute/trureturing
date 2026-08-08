using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void RequiredPrAProjectionRebuildLaneHasSufficientEngineeringBudget()
    {
        var root = FindRepositoryRoot();
        using var reader = File.OpenText(Path.Combine(root, AdmissionWorkflowPath));
        var yaml = new YamlStream();
        yaml.Load(reader);

        var document = Assert.IsType<YamlMappingNode>(Assert.Single(yaml.Documents).RootNode);
        var jobs = CiBudgetMapping(document, "jobs");
        var engineering = CiBudgetMapping(jobs, "candidate-engineering");
        Assert.Equal(
            "Candidate harness engineering checks",
            CiBudgetScalar(engineering, "name"));

        var steps = Assert.IsType<YamlSequenceNode>(CiBudgetNode(engineering, "steps"));
        var rebuild = Assert.Single(
            steps.Children.OfType<YamlMappingNode>(),
            static step =>
                step.Children.TryGetValue(new YamlScalarNode("name"), out var name)
                && name is YamlScalarNode scalar
                && scalar.Value == "Verify required PR-A projection rebuild lane");

        // The lane rebuilds a full Lean report inside this job. Runner timings vary
        // with machine class, so the floor only has to stay far above the observed
        // 15m29s-19m+ range; the workflow itself may budget more. Tracked end state
        // is issue #952: reuse the sibling canonical Lean report instead of
        // rebuilding, after which this floor should be re-derived from measurement.
        var timeout = int.Parse(CiBudgetScalar(engineering, "timeout-minutes"));
        Assert.True(timeout >= 45, $"required PR-A engineering budget is only {timeout} minutes");

        // Detection must not be downgraded (CLAUDE.md rule 20): the lane may not be
        // skipped, softened, or given its own shorter budget, at either level.
        Assert.False(engineering.Children.ContainsKey(new YamlScalarNode("if")));
        Assert.False(engineering.Children.ContainsKey(new YamlScalarNode("continue-on-error")));
        Assert.False(rebuild.Children.ContainsKey(new YamlScalarNode("if")));
        Assert.False(rebuild.Children.ContainsKey(new YamlScalarNode("continue-on-error")));
        Assert.False(rebuild.Children.ContainsKey(new YamlScalarNode("timeout-minutes")));
    }

    private static YamlNode CiBudgetNode(YamlMappingNode mapping, string key)
    {
        Assert.True(mapping.Children.TryGetValue(new YamlScalarNode(key), out var value));
        return value;
    }

    private static YamlMappingNode CiBudgetMapping(YamlMappingNode mapping, string key) =>
        Assert.IsType<YamlMappingNode>(CiBudgetNode(mapping, key));

    private static string CiBudgetScalar(YamlMappingNode mapping, string key) =>
        Assert.IsType<YamlScalarNode>(CiBudgetNode(mapping, key)).Value
        ?? throw new InvalidDataException($"YAML scalar '{key}' has no value.");
}
