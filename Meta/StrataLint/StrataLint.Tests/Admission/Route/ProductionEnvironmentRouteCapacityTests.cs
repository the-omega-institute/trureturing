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
        // A blueprinted module now occupies one structural slot (its .scribe.cs); the
        // emitted .md is a projection SL-003 exempts, so the bucket must already be full
        // for the next module to overflow it.
        var files = BlueprintBucketFiles(RepositoryRules.DirectoryFileLimit);
        var environment = RouteEnvironment(temporary.Path, files);

        var result = environment.Route(["manifest.json"]);

        Assert.False(result.Success);
        Assert.Contains("Blueprint/D5/S0/Carrier", result.Error, StringComparison.Ordinal);
        Assert.Contains("projected occupancy 13 exceeds maximum 12", result.Error, StringComparison.Ordinal);
        Assert.Contains("Carrier=12", result.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("E", "Carrier", "Probe", "result", "json", "", "Evidence/D5/S0/Carrier")]
    [InlineData("C", "2026-07-11", "round-168", "", "markdown", "", "Chronicle/2026/07")]
    [InlineData("L", "Notes", "sample2026paper", "", "markdown", "", "Library/notes")]
    [InlineData("P", "Papers", "D5-P001", "", "recipe", "", "Papers/recipes")]
    public void RouteDoesNotApplyFormalCapacityPreflightToOtherPlanes(
        string plane,
        string domain,
        string module,
        string selector,
        string artifact,
        string tag,
        string targetDirectory)
    {
        using var temporary = RouteRepository(Manifest(plane, domain, module, selector, artifact, tag));
        var files = FullDirectoryFiles(targetDirectory);
        var environment = RouteEnvironment(temporary.Path, files);

        var result = environment.Route(["manifest.json"]);

        Assert.True(result.Success, result.Error);
    }

    [Theory]
    [InlineData("E", "Carrier", "Probe", "result", "json", "")]
    [InlineData("C", "2026-07-11", "round-168", "", "markdown", "")]
    [InlineData("L", "Notes", "sample2026paper", "", "markdown", "")]
    [InlineData("P", "Papers", "D5-P001", "", "recipe", "")]
    public void RouteDoesNotReadCurrentSnapshotForOtherPlanes(
        string plane,
        string domain,
        string module,
        string selector,
        string artifact,
        string tag)
    {
        using var temporary = RouteRepository(Manifest(plane, domain, module, selector, artifact, tag));
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]), null, null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            repository,
            new FakeLeanReportSource(null));

        var result = environment.Route(["manifest.json"]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, repository.ReadCount);
    }

    [Fact]
    public void RouteRejectsFormalBucketWhenBlueprintOriginWouldExceedLimit()
    {
        using var temporary = RouteRepository(Manifest("B", "Carrier", "Probe", "", "markdown", ""));
        var files = LeanBucketFiles(RepositoryRules.DirectoryFileLimit);
        var environment = RouteEnvironment(temporary.Path, files);

        var result = environment.Route(["manifest.json"]);

        Assert.False(result.Success);
        Assert.Contains("D5/S0/Carrier", result.Error, StringComparison.Ordinal);
        Assert.Contains("projected occupancy 13 exceeds maximum 12", result.Error, StringComparison.Ordinal);
        Assert.Contains("Carrier=12", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void RouteRejectsBlueprintBucketWhenBlueprintOriginWouldExceedLimit()
    {
        using var temporary = RouteRepository(Manifest("B", "Carrier", "Probe", "", "markdown", ""));
        // Same arithmetic as the formal-origin case: the emitted .md is exempt, so the
        // module's one structural slot only overflows an already-full bucket.
        var files = BlueprintBucketFiles(RepositoryRules.DirectoryFileLimit);
        var environment = RouteEnvironment(temporary.Path, files);

        var result = environment.Route(["manifest.json"]);

        Assert.False(result.Success);
        Assert.Contains("Blueprint/D5/S0/Carrier", result.Error, StringComparison.Ordinal);
        Assert.Contains("projected occupancy 13 exceeds maximum 12", result.Error, StringComparison.Ordinal);
        Assert.Contains("Carrier=12", result.Error, StringComparison.Ordinal);
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
            index => $"Blueprint/D5/S0/Carrier/Existing{index:D2}.scribe.cs",
            static _ => "<!-- fixture -->\n",
            StringComparer.Ordinal);

    private static Dictionary<string, string> FullDirectoryFiles(string directory) =>
        Enumerable.Range(0, RepositoryRules.DirectoryFileLimit).ToDictionary(
            index => $"{directory}/existing-{index:D2}.fixture",
            static _ => "fixture\n",
            StringComparer.Ordinal);

    private static TemporaryDirectory RouteRepository(string? manifest = null)
    {
        var temporary = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(temporary.Path, "Meta"));
        File.WriteAllText(Path.Combine(temporary.Path, "Meta", "registry.yaml"), TestRegistry.Canonical, new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(temporary.Path, "Meta", "domains.yaml"), TestRegistry.Domains, new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(temporary.Path, "manifest.json"),
            manifest ?? Manifest("F", "Carrier", "Probe", "", "lean", ""),
            new UTF8Encoding(false));
        return temporary;
    }

    private static string Manifest(
        string plane,
        string domain,
        string module,
        string selector,
        string artifact,
        string tag) =>
        $$"""
        {"artifact":"{{artifact}}","domain":"{{domain}}","generality":"G","module":"{{module}}","plane":"{{plane}}","selector":"{{selector}}","tag":"{{tag}}","theory":"D5"}
        """;

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
