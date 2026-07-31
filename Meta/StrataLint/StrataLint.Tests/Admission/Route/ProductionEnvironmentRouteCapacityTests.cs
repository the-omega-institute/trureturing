using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void RouteAllowsProjectedOccupancyAtDirectoryFileLimit()
    {
        using var temporary = RouteRepository();
        var files = LeanBucketFiles(RepositoryRules.DirectoryFileLimit - 1);
        var environment = RouteEnvironment(temporary.Path, files);

        var result = environment.Route(["manifest.json"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"path\": \"D5/S0/Carrier/Probe.lean\"", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void RouteRejectsLeanBucketAboveDirectoryFileLimitWithSiblingCounts()
    {
        using var temporary = RouteRepository();
        var files = LeanBucketFiles(RepositoryRules.DirectoryFileLimit);
        var environment = RouteEnvironment(temporary.Path, files);

        var result = environment.Route(["manifest.json"]);

        Assert.False(result.Success);
        Assert.Contains("SL-003 route: bucket at capacity", result.Error, StringComparison.Ordinal);
        Assert.Contains("projected occupancy 13 exceeds maximum 12", result.Error, StringComparison.Ordinal);
        Assert.Contains("Carrier=12", result.Error, StringComparison.Ordinal);
        Assert.Contains("Conventions=0", result.Error, StringComparison.Ordinal);
        Assert.Contains("bucket at capacity — 只裂不迁", result.Error, StringComparison.Ordinal);
        Assert.Contains("split only", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void RouteRejectsBlueprintBucketWhenModulePairWouldExceedLimit()
    {
        using var temporary = RouteRepository();
        var files = BlueprintBucketFiles(RepositoryRules.DirectoryFileLimit - 1);
        var environment = RouteEnvironment(temporary.Path, files);

        var result = environment.Route(["manifest.json"]);

        Assert.False(result.Success);
        Assert.Contains("Blueprint/D5/S0/Carrier", result.Error, StringComparison.Ordinal);
        Assert.Contains("projected occupancy 13 exceeds maximum 12", result.Error, StringComparison.Ordinal);
        Assert.Contains("Carrier=11", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void RouteCountsOnlyMissingCanonicalOutputs()
    {
        using var temporary = RouteRepository();
        var files = LeanBucketFiles(RepositoryRules.DirectoryFileLimit - 1);
        files["D5/S0/Carrier/Probe.lean"] = "-- existing routed artifact\n";
        foreach (var pair in BlueprintBucketFiles(RepositoryRules.DirectoryFileLimit - 2))
        {
            files[pair.Key] = pair.Value;
        }

        files["Blueprint/D5/S0/Carrier/Probe.md"] = "<!-- existing emission -->\n";
        files["Blueprint/D5/S0/Carrier/Probe.scribe.cs"] = "// existing definition\n";
        var environment = RouteEnvironment(temporary.Path, files);

        var result = environment.Route(["manifest.json"]);

        Assert.True(result.Success, result.Error);
    }

    [Fact]
    public void RouteIgnoresCapacityExcludedDirectories()
    {
        using var temporary = RouteRepository();
        var files = Enumerable.Range(0, RepositoryRules.DirectoryFileLimit + 1).ToDictionary(
            index => $"Meta/Digestion/formalizations/receipt-{index:D2}.v1.json",
            static _ => "{}\n",
            StringComparer.Ordinal);
        var environment = RouteEnvironment(temporary.Path, files);

        var result = environment.Route(["manifest.json"]);

        Assert.True(result.Success, result.Error);
    }

    private static Dictionary<string, string> LeanBucketFiles(int count) =>
        Enumerable.Range(0, count).ToDictionary(
            index => $"D5/S0/Carrier/Existing{index:D2}.lean",
            static _ => "-- fixture\n",
            StringComparer.Ordinal);

    private static Dictionary<string, string> BlueprintBucketFiles(int count) =>
        Enumerable.Range(0, count).ToDictionary(
            index => $"Blueprint/D5/S0/Carrier/Existing{index:D2}.md",
            static _ => "<!-- fixture -->\n",
            StringComparer.Ordinal);

    private static TemporaryDirectory RouteRepository()
    {
        var temporary = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(temporary.Path, "Meta"));
        File.WriteAllText(Path.Combine(temporary.Path, "Meta", "registry.yaml"), TestRegistry.Canonical, new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(temporary.Path, "Meta", "domains.yaml"), TestRegistry.Domains, new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(temporary.Path, "manifest.json"),
            "{\"artifact\":\"lean\",\"domain\":\"Carrier\",\"generality\":\"G\",\"module\":\"Probe\",\"plane\":\"F\",\"selector\":\"\",\"tag\":\"\",\"theory\":\"D5\"}\n",
            new UTF8Encoding(false));
        return temporary;
    }

    private static ProductionCliEnvironment RouteEnvironment(
        string repositoryRoot,
        IReadOnlyDictionary<string, string> files) =>
        new(
            repositoryRoot,
            new FakeRepositoryGateway(
                RawChangeSet.Create([]),
                Snapshot(files),
                Snapshot(files)),
            new FakeLeanReportSource(null));
}
