using System.Text;
using StrataLint.Engine;
using YamlDotNet.RepresentationModel;

namespace StrataLint.ScriptTests;

[ScriptSubject("tools/scripts/workflow/judge-content-address.sh")]
public sealed class JudgeContentAddressTests
{
    private const string SourceAddress =
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string ResolverPath = "tools/scripts/workflow/judge-content-address.sh";
    private const string ExpectedCacheKey =
        "stratalint-judge-binaries-v2-${{ runner.os }}-${{ steps.judge-address.outputs.runtime }}-${{ steps.judge-address.outputs.address }}";

    [Fact]
    public void JudgeBinaryCacheKeyIncludesExecutingDotNetRuntimeIdentity()
    {
        var root = TestRepositoryLayout.FindRoot();
        var resolver = Path.Combine(root, ResolverPath);
        var first = Resolve(resolver, root);
        var second = Resolve(resolver, root);
        Assert.Equal(Environment.Version.ToString(), first["runtime"]);
        Assert.Equal(first["runtime"], second["runtime"]);
        Assert.Equal(first["address"], second["address"]);
        Assert.Matches("^[0-9a-f]{64}$", first["address"]);

        var workflow = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create(".github/workflows/ci.yml"));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var addressStepCount = 0;
        var cacheKeys = new List<string>();
        foreach (var job in jobs.Children.Values.OfType<YamlMappingNode>())
        {
            if (!job.Children.TryGetValue(new YamlScalarNode("steps"), out var rawSteps))
            {
                continue;
            }

            var steps = Assert.IsType<YamlSequenceNode>(rawSteps).Children
                .OfType<YamlMappingNode>()
                .ToArray();
            var sdkIndex = Array.FindIndex(steps, IsSetupDotnetStep);
            var addressIndex = Array.FindIndex(steps, IsJudgeAddressStep);
            if (addressIndex >= 0)
            {
                addressStepCount++;
                Assert.True(sdkIndex >= 0 && sdkIndex < addressIndex);
                var run = RuntimeIdentityScalar(steps[addressIndex], "run");
                Assert.Contains(ResolverPath, run, StringComparison.Ordinal);
            }

            cacheKeys.AddRange(steps
                .Where(IsJudgeCacheStep)
                .Select(step => RuntimeIdentityScalar(
                    Assert.IsType<YamlMappingNode>(step.Children[new YamlScalarNode("with")]),
                    "key")));
        }

        Assert.Equal(3, addressStepCount);
        Assert.Equal(3, cacheKeys.Count);
        Assert.All(cacheKeys, key => Assert.Equal(ExpectedCacheKey, key));
        Assert.All(cacheKeys, key =>
        {
            var rendered = key.Replace(
                "${{ steps.judge-address.outputs.runtime }}",
                first["runtime"],
                StringComparison.Ordinal);
            Assert.Contains(first["runtime"], rendered, StringComparison.Ordinal);
        });
    }

    private static IReadOnlyDictionary<string, string> Resolve(string resolver, string root)
    {
        var result = TestProcessRunner.Run(
            "/bin/bash",
            [resolver, SourceAddress],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
        var output = Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError);
        Assert.True(result.ExitCode == 0, output);
        return output.Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Select(static line => line.Split('=', 2))
            .ToDictionary(static pair => pair[0], static pair => pair[1], StringComparer.Ordinal);
    }

    private static bool IsSetupDotnetStep(YamlMappingNode step) =>
        step.Children.TryGetValue(new YamlScalarNode("uses"), out var uses)
        && Assert.IsType<YamlScalarNode>(uses).Value == "actions/setup-dotnet@v4";

    private static bool IsJudgeAddressStep(YamlMappingNode step) =>
        step.Children.TryGetValue(new YamlScalarNode("id"), out var id)
        && Assert.IsType<YamlScalarNode>(id).Value == "judge-address";

    private static bool IsJudgeCacheStep(YamlMappingNode step) =>
        step.Children.TryGetValue(new YamlScalarNode("uses"), out var uses)
        && Assert.IsType<YamlScalarNode>(uses).Value is "actions/cache/restore@v4" or "actions/cache/save@v4"
        && step.Children.TryGetValue(new YamlScalarNode("with"), out var rawWith)
        && Assert.IsType<YamlMappingNode>(rawWith).Children.TryGetValue(new YamlScalarNode("key"), out var key)
        && Assert.IsType<YamlScalarNode>(key).Value?.StartsWith("stratalint-judge-binaries-", StringComparison.Ordinal) == true;

    private static string RuntimeIdentityScalar(YamlMappingNode node, string key) =>
        Assert.IsType<YamlScalarNode>(node.Children[new YamlScalarNode(key)]).Value ?? string.Empty;
}
