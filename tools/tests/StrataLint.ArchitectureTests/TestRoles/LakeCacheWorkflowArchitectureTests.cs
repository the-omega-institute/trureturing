using YamlDotNet.RepresentationModel;
using StrataLint.Engine;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class LakeCacheWorkflowArchitectureTests
{
    private const string DependencyKey =
        "${{ runner.os }}-${{ runner.arch }}-lake-deps-v1-${{ steps.lean-report-input.outputs.config_sha256 }}";
    private const string BuildKey =
        "${{ runner.os }}-${{ runner.arch }}-lake-build-v1-${{ steps.lean-report-input.outputs.config_sha256 }}-${{ steps.lean-report-input.outputs.sources_sha256 }}";
    private const string DependencyRestoreKey = DependencyKey;
    private const string BuildRestoreKey =
        "${{ runner.os }}-${{ runner.arch }}-lake-build-v1-${{ steps.lean-report-input.outputs.config_sha256 }}-";

    // 原先此契约跨两个站点(ci.yml 的 admission job 与已删除的 theory-ingest)。
    // 消化退出 CI 后只剩一个站点,但五条断言里两条完全不依赖站点(纯合成键模板推理)、
    // 两条是逐站点的——故契约保留并接到 ci.yml,不随被删站点一起静默消失。
    [Fact]
    public void AdmissionWorkflowHonoursTheLakeCacheContract() =>
        AssertLakeCacheContract(
            TestRepositoryLayout.ReadAllText(
                RepositoryRelativePath.Create(".github/workflows/ci.yml")));

    private static void AssertLakeCacheContract(string admissionWorkflow)
    {
        var workflows = new[] { admissionWorkflow };
        var steps = ParseLakeCacheSteps(workflows).ToArray();
        AssertLakeCacheSitesUseTheSamePartitionedKeyTemplates(steps);
        AssertConfigAndSourceChangesInvalidateOnlyTheirOwningLayers();
        AssertRestorePrefixesCannotCrossConfigurationBoundaries();
        AssertLakeSavesUseExactConjunctiveProductionMissGuards(steps);
        AssertWorkflowsExposeBothExistingClosureHashes(workflows);
    }

    private static void AssertLakeCacheSitesUseTheSamePartitionedKeyTemplates(
        IReadOnlyCollection<CacheStep> steps)
    {
        var dependencies = steps.Where(static step => IsLakeDependencyPath(step.Path)).ToArray();
        var builds = steps.Where(static step => step.Path == "candidate/.lake/build").ToArray();

        // 不写死站点数。原先断言恰 6 个(3 依赖 + 3 构建),那是 ci.yml 与已删除的
        // theory-ingest 两站点之和——写死使「增删一个站点」被迫改测试
        // (CLAUDE.md 商余结构)。改判结构:每个缓存步骤都必须落入两层之一、
        // 不留未分类者,且两层各自既有 restore 又有 save。
        Assert.NotEmpty(steps);
        Assert.Equal(steps.Count, dependencies.Length + builds.Length);
        foreach (var layer in new[] { dependencies, builds })
        {
            Assert.Contains(
                layer,
                static step => step.Uses.StartsWith("actions/cache/restore@", StringComparison.Ordinal));
            Assert.Contains(
                layer,
                static step => !step.Uses.StartsWith("actions/cache/restore@", StringComparison.Ordinal));
        }

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

    private static void AssertConfigAndSourceChangesInvalidateOnlyTheirOwningLayers()
    {
        const string configA = "config-a";
        const string configB = "config-b";
        const string sourcesA = "sources-a";
        const string sourcesB = "sources-b";

        var dependencyA = RenderLakeCacheKey(DependencyKey, configA, sourcesA);
        Assert.Equal(dependencyA, RenderLakeCacheKey(DependencyKey, configA, sourcesB));
        Assert.NotEqual(dependencyA, RenderLakeCacheKey(DependencyKey, configB, sourcesA));

        var buildA = RenderLakeCacheKey(BuildKey, configA, sourcesA);
        Assert.NotEqual(buildA, RenderLakeCacheKey(BuildKey, configA, sourcesB));
        Assert.NotEqual(buildA, RenderLakeCacheKey(BuildKey, configB, sourcesA));
        Assert.Contains($"-{configA}-{sourcesA}", buildA, StringComparison.Ordinal);
    }

    private static void AssertRestorePrefixesCannotCrossConfigurationBoundaries()
    {
        const string configA = "config-a";
        const string configB = "config-b";

        var dependencyRestoreA = RenderLakeCacheKey(DependencyRestoreKey, configA, "ignored");
        var dependencyKeyB = RenderLakeCacheKey(DependencyKey, configB, "ignored");
        Assert.False(dependencyKeyB.StartsWith(dependencyRestoreA, StringComparison.Ordinal));

        var buildRestoreA = RenderLakeCacheKey(BuildRestoreKey, configA, "ignored");
        Assert.StartsWith(buildRestoreA, RenderLakeCacheKey(BuildKey, configA, "other-sources"), StringComparison.Ordinal);
        Assert.False(RenderLakeCacheKey(BuildKey, configB, "other-sources").StartsWith(buildRestoreA, StringComparison.Ordinal));
    }

    private static void AssertLakeSavesUseExactConjunctiveProductionMissGuards(
        IEnumerable<CacheStep> steps)
    {
        var saves = steps
            .Where(static step => step.Uses.StartsWith("actions/cache/save@", StringComparison.Ordinal))
            .ToArray();
        Assert.Equal(2, saves.Length);

        var dependencies = Assert.Single(saves, static step => IsLakeDependencyPath(step.Path));
        var build = Assert.Single(saves, static step => step.Path == "candidate/.lake/build");
        Assert.Equal(ExactLakeCacheSaveCondition("lake-deps-cache"), dependencies.Condition);
        Assert.Equal(ExactLakeCacheSaveCondition("lake-build-cache"), build.Condition);
    }

    private static void AssertWorkflowsExposeBothExistingClosureHashes(
        IEnumerable<string> workflows)
    {
        foreach (var workflow in workflows)
        {
            var resolve = Assert.Single(
                ParseWorkflowSteps(workflow),
                static step => LakeCacheScalar(step, "id") == "lean-report-input");
            var script = LakeCacheScalar(resolve, "run");
            Assert.Contains("sources_sha256", script, StringComparison.Ordinal);
            Assert.Contains("config_sha256", script, StringComparison.Ordinal);
            Assert.Contains("echo \"sources_sha256=$sources_sha256\" >> \"$GITHUB_OUTPUT\"", script, StringComparison.Ordinal);
            Assert.Contains("echo \"config_sha256=$config_sha256\" >> \"$GITHUB_OUTPUT\"", script, StringComparison.Ordinal);
        }
    }

    private static IEnumerable<CacheStep> ParseLakeCacheSteps(IEnumerable<string> workflows) =>
        workflows.SelectMany(workflow => ParseWorkflowSteps(workflow)
            .Where(static step => LakeCacheScalar(step, "uses").StartsWith("actions/cache/", StringComparison.Ordinal))
            .Where(static step => LakeCacheScalar(LakeCacheMapping(step, "with"), "path").Contains("candidate/.lake", StringComparison.Ordinal))
            .Select(step =>
            {
                var with = LakeCacheMapping(step, "with");
                return new CacheStep(
                    LakeCacheScalar(step, "name"),
                    LakeCacheScalar(step, "uses"),
                    LakeCacheScalar(with, "path").Trim(),
                    LakeCacheScalar(with, "key"),
                    LakeCacheScalar(with, "restore-keys").Trim(),
                    LakeCacheScalar(step, "if"));
            }));

    private static bool IsLakeDependencyPath(string path) =>
        path.Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .SequenceEqual(
                [
                    "candidate/.lake/packages",
                    "candidate/.lake/config",
                    "candidate/.lake/.stratalint-lean-cache-stamp.json",
                    "~/.cache/mathlib",
                ],
                StringComparer.Ordinal);

    private static string ExactLakeCacheSaveCondition(string cacheStepId) =>
        $"success() && steps.report-reuse.outcome != 'success'"
        + $" && steps.{cacheStepId}.outputs.cache-hit != 'true'"
        + " && github.event_name == 'push' && github.ref == 'refs/heads/dev'";

    private static string RenderLakeCacheKey(string template, string config, string sources) => template
        .Replace("${{ runner.os }}", "Linux", StringComparison.Ordinal)
        .Replace("${{ runner.arch }}", "ARM64", StringComparison.Ordinal)
        .Replace("${{ steps.lean-report-input.outputs.config_sha256 }}", config, StringComparison.Ordinal)
        .Replace("${{ steps.lean-report-input.outputs.sources_sha256 }}", sources, StringComparison.Ordinal);

    private static IEnumerable<YamlMappingNode> ParseWorkflowSteps(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var root = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = LakeCacheMapping(root, "jobs");
        return jobs.Children.Values.OfType<YamlMappingNode>()
            .Where(static job => job.Children.ContainsKey(new YamlScalarNode("steps")))
            .SelectMany(static job => Assert.IsType<YamlSequenceNode>(
                job.Children[new YamlScalarNode("steps")]).Children.OfType<YamlMappingNode>());
    }

    private static YamlMappingNode LakeCacheMapping(YamlMappingNode node, string key) =>
        node.Children.TryGetValue(new YamlScalarNode(key), out var value)
            ? Assert.IsType<YamlMappingNode>(value)
            : new YamlMappingNode();

    private static string LakeCacheScalar(YamlMappingNode node, string key) =>
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
