using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed class LakeCacheWorkflowTests
{
    private const string DependencyKey =
        "${{ runner.os }}-${{ runner.arch }}-lake-deps-v1-${{ steps.lean-report-input.outputs.config_sha256 }}";
    private const string BuildKey =
        "${{ runner.os }}-${{ runner.arch }}-lake-build-v1-${{ steps.lean-report-input.outputs.config_sha256 }}-${{ steps.lean-report-input.outputs.sources_sha256 }}";
    private const string DependencyRestoreKey = DependencyKey;
    private const string BuildRestoreKey =
        "${{ runner.os }}-${{ runner.arch }}-lake-build-v1-${{ steps.lean-report-input.outputs.config_sha256 }}-";

    [Fact]
    public void LakeCacheSitesUseTheSamePartitionedKeyTemplates()
    {
        var steps = LakeCacheSteps().ToArray();
        Assert.Equal(6, steps.Length);

        var dependencies = steps.Where(static step => IsDependencyPath(step.Path)).ToArray();
        var builds = steps.Where(static step => step.Path == "candidate/.lake/build").ToArray();
        Assert.Equal(3, dependencies.Length);
        Assert.Equal(3, builds.Length);

        Assert.All(dependencies, step => Assert.Equal(DependencyKey, step.Key));
        Assert.All(builds, step => Assert.Equal(BuildKey, step.Key));
        Assert.DoesNotContain("sources_sha256", DependencyKey, StringComparison.Ordinal);
        Assert.Contains("config_sha256 }}-${{ steps.lean-report-input.outputs.sources_sha256", BuildKey, StringComparison.Ordinal);

        Assert.All(
            dependencies.Where(static step => step.Uses.StartsWith("actions/cache/restore@", StringComparison.Ordinal)),
            step => Assert.Equal(DependencyRestoreKey, step.RestoreKeys));
        Assert.All(
            builds.Where(static step => step.Uses.StartsWith("actions/cache/restore@", StringComparison.Ordinal)),
            step => Assert.Equal(BuildRestoreKey, step.RestoreKeys));
    }

    [Fact]
    public void ConfigAndSourceChangesInvalidateOnlyTheirOwningLayers()
    {
        const string configA = "config-a";
        const string configB = "config-b";
        const string sourcesA = "sources-a";
        const string sourcesB = "sources-b";

        var dependencyA = Render(DependencyKey, configA, sourcesA);
        Assert.Equal(dependencyA, Render(DependencyKey, configA, sourcesB));
        Assert.NotEqual(dependencyA, Render(DependencyKey, configB, sourcesA));

        var buildA = Render(BuildKey, configA, sourcesA);
        Assert.NotEqual(buildA, Render(BuildKey, configA, sourcesB));
        Assert.NotEqual(buildA, Render(BuildKey, configB, sourcesA));
        Assert.Contains($"-{configA}-{sourcesA}", buildA, StringComparison.Ordinal);
    }

    [Fact]
    public void RestorePrefixesCannotCrossConfigurationBoundaries()
    {
        const string configA = "config-a";
        const string configB = "config-b";

        var dependencyRestoreA = Render(DependencyRestoreKey, configA, "ignored");
        var dependencyKeyB = Render(DependencyKey, configB, "ignored");
        Assert.False(dependencyKeyB.StartsWith(dependencyRestoreA, StringComparison.Ordinal));

        var buildRestoreA = Render(BuildRestoreKey, configA, "ignored");
        Assert.StartsWith(buildRestoreA, Render(BuildKey, configA, "other-sources"), StringComparison.Ordinal);
        Assert.False(Render(BuildKey, configB, "other-sources").StartsWith(buildRestoreA, StringComparison.Ordinal));
    }

    [Fact]
    public void LakeSavesUseExactConjunctiveProductionMissGuards()
    {
        var saves = LakeCacheSteps()
            .Where(static step => step.Uses.StartsWith("actions/cache/save@", StringComparison.Ordinal))
            .ToArray();
        Assert.Equal(2, saves.Length);

        var dependencies = Assert.Single(saves, static step => IsDependencyPath(step.Path));
        var build = Assert.Single(saves, static step => step.Path == "candidate/.lake/build");
        Assert.Equal(ExactSaveCondition("lake-deps-cache"), dependencies.Condition);
        Assert.Equal(ExactSaveCondition("lake-build-cache"), build.Condition);
    }

    [Fact]
    public void WorkflowsExposeBothExistingClosureHashes()
    {
        foreach (var workflow in new[] { ".github/workflows/ci.yml", ".github/workflows/theory-ingest.yml" })
        {
            var resolve = Assert.Single(
                Steps(workflow),
                static step => Scalar(step, "id") == "lean-report-input");
            var script = Scalar(resolve, "run");
            Assert.Contains("sources_sha256", script, StringComparison.Ordinal);
            Assert.Contains("config_sha256", script, StringComparison.Ordinal);
            Assert.Contains("echo \"sources_sha256=$sources_sha256\" >> \"$GITHUB_OUTPUT\"", script, StringComparison.Ordinal);
            Assert.Contains("echo \"config_sha256=$config_sha256\" >> \"$GITHUB_OUTPUT\"", script, StringComparison.Ordinal);
        }
    }

    private static IEnumerable<CacheStep> LakeCacheSteps() =>
        new[] { ".github/workflows/ci.yml", ".github/workflows/theory-ingest.yml" }
            .SelectMany(workflow => Steps(workflow)
                .Where(static step => Scalar(step, "uses").StartsWith("actions/cache/", StringComparison.Ordinal))
                .Where(static step => Scalar(Mapping(step, "with"), "path").Contains("candidate/.lake", StringComparison.Ordinal))
                .Select(step =>
                {
                    var with = Mapping(step, "with");
                    return new CacheStep(
                        Scalar(step, "name"),
                        Scalar(step, "uses"),
                        Scalar(with, "path").Trim(),
                        Scalar(with, "key"),
                        Scalar(with, "restore-keys").Trim(),
                        Scalar(step, "if"));
                }));

    private static bool IsDependencyPath(string path) =>
        path.Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .SequenceEqual(
                [
                    "candidate/.lake/packages",
                    "candidate/.lake/config",
                    "candidate/.lake/.stratalint-lean-cache-stamp.json",
                    "~/.cache/mathlib",
                ],
                StringComparer.Ordinal);

    private static string ExactSaveCondition(string cacheStepId) =>
        $"success() && steps.report-reuse.outcome != 'success'"
        + $" && steps.{cacheStepId}.outputs.cache-hit != 'true'"
        + " && github.event_name == 'push' && github.ref == 'refs/heads/dev'";

    private static string Render(string template, string config, string sources) => template
        .Replace("${{ runner.os }}", "Linux", StringComparison.Ordinal)
        .Replace("${{ runner.arch }}", "ARM64", StringComparison.Ordinal)
        .Replace("${{ steps.lean-report-input.outputs.config_sha256 }}", config, StringComparison.Ordinal)
        .Replace("${{ steps.lean-report-input.outputs.sources_sha256 }}", sources, StringComparison.Ordinal);

    private static IEnumerable<YamlMappingNode> Steps(string relativePath)
    {
        var path = Path.Combine(TestRepositoryLayout.FindRoot(), relativePath);
        var stream = new YamlStream();
        stream.Load(new StringReader(File.ReadAllText(path)));
        var root = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Mapping(root, "jobs");
        return jobs.Children.Values.OfType<YamlMappingNode>()
            .Where(static job => job.Children.ContainsKey(new YamlScalarNode("steps")))
            .SelectMany(static job => Assert.IsType<YamlSequenceNode>(
                job.Children[new YamlScalarNode("steps")]).Children.OfType<YamlMappingNode>());
    }

    private static YamlMappingNode Mapping(YamlMappingNode node, string key) =>
        node.Children.TryGetValue(new YamlScalarNode(key), out var value)
            ? Assert.IsType<YamlMappingNode>(value)
            : new YamlMappingNode();

    private static string Scalar(YamlMappingNode node, string key) =>
        node.Children.TryGetValue(new YamlScalarNode(key), out var value)
            ? Assert.IsType<YamlScalarNode>(value).Value ?? string.Empty
            : string.Empty;

    private sealed record CacheStep(
        string Name,
        string Uses,
        string Path,
        string Key,
        string RestoreKeys,
        string Condition);
}
