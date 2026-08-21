using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class Sl015AdditionalEdgeScopeTests
{
    private const string UnrelatedPath = "notes/sl015-unrelated.txt";
    private const string RuleImplementationPath =
        "tools/StrataLint.Engine/Coordinates/RepositoryPathPolicy.cs";
    private const string PathPolicyMessage =
        "path is outside the registry artifact kind/selector whitelist";
    private const string CompositionMessage =
        "Blueprint composition root allows at most one direct .csproj";

    internal static void RunEvaluatePathFindingsScopeProbe()
    {
        const string path = "Evidence/D5/S0/Carrier/Probe.unknown.json";
        var unrelated = HistoricalPath(path);
        SetDelta(unrelated, UnrelatedPath);
        AssertNoFinding(Execute(unrelated, UnrelatedPath), path, PathPolicyMessage);

        var changed = HistoricalPath(path);
        AssertFinding(Execute(changed, path), path, PathPolicyMessage);

        var implementation = HistoricalPath(path);
        AssertFinding(Execute(implementation, RuleImplementationPath), path, PathPolicyMessage);
    }

    internal static void RunEvaluateCompositionFindingsScopeProbe()
    {
        const string first = "Blueprint/One.csproj";
        const string second = "Blueprint/Two.csproj";
        var unrelated = CompositionHistory(first, second);
        SetDelta(unrelated, UnrelatedPath);
        AssertNoFinding(Execute(unrelated, UnrelatedPath), second, CompositionMessage);

        var oneChanged = CompositionHistory(first, second);
        SetDelta(oneChanged, first, "<Project />\n", "<Project><PropertyGroup /></Project>\n");
        AssertFinding(Execute(oneChanged, first), second, CompositionMessage);

        var bothChanged = CompositionHistory(first, second);
        SetDelta(bothChanged, first, "<Project />\n", "<Project><PropertyGroup /></Project>\n");
        SetDelta(bothChanged, second, "<Project />\n", "<Project><ItemGroup /></Project>\n");
        AssertFinding(Execute(bothChanged, first, second), second, CompositionMessage);

        var implementation = CompositionHistory(first, second);
        AssertFinding(Execute(implementation, RuleImplementationPath), second, CompositionMessage);
    }

    private static RuleFixture HistoricalPath(string path)
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, path, "{}\n");
        return fixture;
    }

    private static RuleFixture CompositionHistory(string first, string second)
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, first, "<Project />\n");
        SetHistorical(fixture, second, "<Project />\n");
        return fixture;
    }

    private static CompletedRuleSet Execute(RuleFixture fixture, params string[] changedPaths) =>
        Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create(changedPaths)))).Capability;

    private static void SetHistorical(RuleFixture fixture, string path, string text)
    {
        fixture.Files[path] = text;
        fixture.Baseline[path] = text;
        fixture.ForkPoint[path] = text;
    }

    private static void SetDelta(RuleFixture fixture, string path) =>
        SetDelta(fixture, path, "base\n", "candidate\n");

    private static void SetDelta(RuleFixture fixture, string path, string baseline, string current)
    {
        fixture.Baseline[path] = baseline;
        fixture.ForkPoint[path] = baseline;
        fixture.Files[path] = current;
    }

    private static void AssertFinding(CompletedRuleSet result, string path, string message) =>
        Assert.Contains(result.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Path == path
            && diagnostic.Message.Contains(message, StringComparison.Ordinal));

    private static void AssertNoFinding(CompletedRuleSet result, string path, string message) =>
        Assert.DoesNotContain(result.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Path == path
            && diagnostic.Message.Contains(message, StringComparison.Ordinal));
}
