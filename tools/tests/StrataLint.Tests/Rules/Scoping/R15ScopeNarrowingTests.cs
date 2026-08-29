using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class R15ScopeNarrowingTests
{
    private const string UnrelatedLeanPath = RuleFixture.ValuesBindingPath;
    private const string RuleImplementationPath =
        "tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs";

    [Fact]
    [BaseFactScopeProbe(1)]
    public void Sl001HistoricalImportFindingSurvivesUnrelatedLeanDelta()
    {
        AssertThreeFaces(
            ImportHistory,
            1,
            "stratum closure may not import",
            RuleFixture.RingPath,
            RuleImplementationPath);

        const string targetPath = "D5/S1/Upper/High.lean";
        var targetDelta = ImportHistory();
        AssertFinding(
            Execute(targetDelta, targetPath),
            1,
            "stratum closure may not import",
            RuleFixture.RingPath);

        var bothDelta = ImportHistory();
        AssertFinding(
            Execute(bothDelta, RuleFixture.RingPath, targetPath),
            1,
            "stratum closure may not import",
            RuleFixture.RingPath);
    }

    [Fact]
    [BaseFactScopeProbe(2)]
    public void Sl002HistoricalSorryFindingSurvivesUnrelatedLeanDelta()
    {
        AssertThreeFaces(
            () => SorryHistory(),
            2,
            "sorryAx occurs in declaration closure",
            RuleFixture.RingPath,
            RuleImplementationPath);

        const string dependencyPath = "D5/S0/Carrier/SorryDependency.lean";
        var dependencyDelta = SorryHistory(dependencyPath);
        AssertFinding(
            Execute(dependencyDelta, dependencyPath),
            2,
            "sorryAx occurs in declaration closure",
            RuleFixture.RingPath);

        var bothDelta = SorryHistory(dependencyPath);
        AssertFinding(
            Execute(bothDelta, RuleFixture.RingPath, dependencyPath),
            2,
            "sorryAx occurs in declaration closure",
            RuleFixture.RingPath);
    }

    [Fact]
    [BaseFactScopeProbe(10)]
    public void Sl010HistoricalGeneralityFindingSurvivesUnrelatedLeanDelta()
    {
        AssertThreeFaces(
            GeneralityHistory,
            10,
            "G artifact imports I fact",
            RuleFixture.RingPath,
            RuleImplementationPath);

        var targetDelta = GeneralityHistory();
        AssertFinding(
            Execute(targetDelta, RuleFixture.NotationPath),
            10,
            "G artifact imports I fact",
            RuleFixture.RingPath);

        var bothDelta = GeneralityHistory();
        AssertFinding(
            Execute(bothDelta, RuleFixture.RingPath, RuleFixture.NotationPath),
            10,
            "G artifact imports I fact",
            RuleFixture.RingPath);
    }

    [Fact]
    [BaseFactScopeProbe(11)]
    public void Sl011HistoricalDomainFindingSurvivesUnrelatedLeanDelta()
    {
        const string historicalPath = "D5/S0/Unknown/Bad.lean";
        AssertThreeFaces(
            DomainHistory,
            11,
            "domain 'Unknown' is not controlled",
            historicalPath,
            RuleImplementationPath);

        var policyDelta = DomainHistory();
        AssertFinding(
            Execute(policyDelta, "Meta/domains.yaml"),
            11,
            "domain 'Unknown' is not controlled",
            historicalPath);

        var bothDelta = DomainHistory();
        AssertFinding(
            Execute(bothDelta, historicalPath, "Meta/domains.yaml"),
            11,
            "domain 'Unknown' is not controlled",
            historicalPath);
    }

    [Fact]
    [BaseFactScopeProbe(17)]
    public void Sl017LiteratureFindingSurvivesUnrelatedLeanDelta()
    {
        const string invalidQueries = """
            schema_version: 1
            queries:
              - id: bad-query
                target_gid: D5/S0/Carrier/Ring
            """;
        RuleFixture Fixture() {
            var fixture = AnchorHistory();
            SetHistorical(fixture, "Library/queries.yaml", invalidQueries);
            return fixture;
        }

        var unrelated = Fixture();
        AssertNoFinding(
            Execute(unrelated, UnrelatedLeanPath),
            17,
            "invalid or duplicate query id",
            "Library/queries.yaml");

        var changed = Fixture();
        AssertFinding(
            Execute(changed, "Library/queries.yaml"),
            17,
            "invalid or duplicate query id",
            "Library/queries.yaml");

        var implementation = Fixture();
        AssertFinding(
            Execute(implementation, "tools/StrataLint.Engine/Rules/Anchors/AnchorReferenceRule.cs"),
            17,
            "invalid or duplicate query id",
            "Library/queries.yaml");
    }

    [Fact]
    [BaseFactScopeProbe(18)]
    public void Sl018HistoricalNoncanonicalValuesPathSurvivesEnvironmentDelta()
    {
        const string historicalPath = "Evidence/D5/values.result.json";
        const string message = "canonical values projection must be Evidence/D5/values.json";

        var unrelated = ValuesPathHistory(historicalPath);
        AssertNoFinding(Execute(unrelated, "global.json"), 18, message, historicalPath);

        var changed = ValuesPathHistory(historicalPath);
        AssertFinding(Execute(changed, historicalPath), 18, message, historicalPath);

        var implementation = ValuesPathHistory(historicalPath);
        AssertFinding(
            Execute(
                implementation,
                "tools/StrataLint.Engine/Rules/RepositoryRules.Content.cs"),
            18,
            message,
            historicalPath);
    }

    [Fact]
    [BaseFactScopeProbe(19)]
    public void Sl019HistoricalAnomalyFindingSurvivesUnrelatedJsonDelta()
    {
        const string historicalPath = "Evidence/D5/S0/Carrier/Historical.run.json";
        const string message = "unknown anomaly-bearing schema";

        var unrelated = AnomalyHistory(historicalPath);
        const string unrelatedPath = "Evidence/D5/S0/Carrier/Unrelated.run.json";
        SetHistorical(unrelated, unrelatedPath, "{}\n");
        AssertNoFinding(Execute(unrelated, unrelatedPath), 19, message, historicalPath);

        var changed = AnomalyHistory(historicalPath);
        AssertFinding(Execute(changed, historicalPath), 19, message, historicalPath);

        var implementation = AnomalyHistory(historicalPath);
        AssertFinding(
            Execute(
                implementation,
                "tools/StrataLint.Engine/Rules/RepositoryRules.StructuredScan.cs"),
            19,
            message,
            historicalPath);

        var taskSetDelta = AnomalyHistory(historicalPath);
        AddHistoricalTask(taskSetDelta);
        AssertFinding(
            Execute(taskSetDelta, RuleFixture.ValuesBindingPath),
            19,
            message,
            historicalPath);

        var bothDelta = AnomalyHistory(historicalPath);
        AddHistoricalTask(bothDelta);
        AssertFinding(
            Execute(bothDelta, historicalPath, RuleFixture.ValuesBindingPath),
            19,
            message,
            historicalPath);
    }

    [Fact]
    public void Sl019ReplaysWhenPolicyChangesAlongsideTaskPreservingLeanEdit()
    {
        const string artifactPath = "Evidence/D5/S0/Carrier/Result.spec.json";
        const string task = "/-- TASK D5-T0097\n    historical task. -/\n";
        const string anomaly = "{\"anomaly\":\"fixture drift\",\"case_id\":\"D5-T0098\"}\n";
        var fixture = new RuleFixture();
        fixture.Baseline[RuleFixture.RingPath] += task;
        fixture.ForkPoint[RuleFixture.RingPath] += task;
        fixture.Files[RuleFixture.RingPath] = fixture.Baseline[RuleFixture.RingPath]
            .Replace("Nat := 0", "Nat := 1", StringComparison.Ordinal);
        fixture.Files[artifactPath] = anomaly;
        fixture.Baseline[artifactPath] = anomaly;
        fixture.ForkPoint[artifactPath] = anomaly;
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical.Replace(
            "      - \"legacy\"\n",
            "      - \"legacy\"\n      - \"spec\"\n",
            StringComparison.Ordinal);

        var changes = RawChangeSet.Create([RuleFixture.RingPath, "Meta/registry.yaml"]);
        var policy = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(fixture.Files["Meta/registry.yaml"]),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(changes, policy))).Capability;

        Assert.Contains(RuleId.CreateKnown(19), completed.ExecutedRules);
        AssertFinding(completed, 19, "unledgered anomaly", artifactPath);
    }

    [Fact]
    public void Sl019ReplaysWhenAnyJudgeSourceChangesAlongsideTaskPreservingLeanEdit()
    {
        const string artifactPath = "Evidence/D5/S0/Carrier/Result.run.json";
        const string helperPath = "tools/StrataLint.Engine/Coordinates/RegistryPolicy.cs";
        const string task = "/-- TASK D5-T0097\n    historical task. -/\n";
        const string anomaly = "{\"anomaly\":\"fixture drift\",\"case_id\":\"D5-T0098\"}\n";
        const string helperSource = "namespace StrataLint.Engine;\n";
        var fixture = new RuleFixture();
        fixture.Baseline[RuleFixture.RingPath] += task;
        fixture.ForkPoint[RuleFixture.RingPath] += task;
        fixture.Files[RuleFixture.RingPath] = fixture.Baseline[RuleFixture.RingPath]
            .Replace("Nat := 0", "Nat := 1", StringComparison.Ordinal);
        fixture.Files[artifactPath] = anomaly;
        fixture.Baseline[artifactPath] = anomaly;
        fixture.ForkPoint[artifactPath] = anomaly;
        fixture.Files[helperPath] = helperSource.Replace(";", "; ", StringComparison.Ordinal);
        fixture.Baseline[helperPath] = helperSource;
        fixture.ForkPoint[helperPath] = helperSource;

        var changes = RawChangeSet.Create([RuleFixture.RingPath, helperPath]);
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(changes))).Capability;

        Assert.Contains(RuleId.CreateKnown(19), completed.ExecutedRules);
        AssertFinding(completed, 19, "unledgered anomaly", artifactPath);
    }

    [Fact]
    public void Sl019ReplaysWhenTaskMovesFromD5IntoTrureturingLean()
    {
        const string rootPath = "Trureturing.lean";
        const string artifactPath = "Evidence/D5/S0/Carrier/TaskMove.run.json";
        const string task = "/-- TASK D5-T0099\n    historical task. -/\n";
        const string anomaly = "{\"anomaly\":\"fixture drift\",\"case_id\":\"D5-T0099\"}\n";
        var fixture = new RuleFixture();
        fixture.Baseline[RuleFixture.RingPath] += task;
        fixture.ForkPoint[RuleFixture.RingPath] += task;
        fixture.Files[rootPath] = task;
        fixture.Baseline[rootPath] = "import D5\n";
        fixture.ForkPoint[rootPath] = "import D5\n";
        fixture.Reports[rootPath] = new LeanFileReport([], []);
        fixture.BaselineReports[rootPath] = new LeanFileReport([], []);
        fixture.Files[artifactPath] = anomaly;
        fixture.Baseline[artifactPath] = anomaly;
        fixture.ForkPoint[artifactPath] = anomaly;

        var completed = Execute(fixture, RuleFixture.RingPath, rootPath);

        Assert.Contains(RuleId.CreateKnown(19), completed.ExecutedRules);
        AssertFinding(completed, 19, "unledgered anomaly", artifactPath);
    }

    [Fact]
    public void Sl019ReplaysWhenBlueprintScribeSourceChangesAlongsideTaskPreservingLeanEdit()
    {
        const string artifactPath = "Evidence/D5/S0/Carrier/ScribeSource.run.json";
        const string scribePath = "Blueprint/D5/S0/Carrier/Result.scribe.cs";
        const string task = "/-- TASK D5-T0097\n    historical task. -/\n";
        const string anomaly = "{\"anomaly\":\"fixture drift\",\"case_id\":\"D5-T0098\"}\n";
        const string scribeSource = "namespace Trureturing.Blueprint;\n";
        var fixture = new RuleFixture();
        fixture.Baseline[RuleFixture.RingPath] += task;
        fixture.ForkPoint[RuleFixture.RingPath] += task;
        fixture.Files[RuleFixture.RingPath] = fixture.Baseline[RuleFixture.RingPath]
            .Replace("Nat := 0", "Nat := 1", StringComparison.Ordinal);
        fixture.Files[artifactPath] = anomaly;
        fixture.Baseline[artifactPath] = anomaly;
        fixture.ForkPoint[artifactPath] = anomaly;
        fixture.Files[scribePath] = scribeSource.Replace(";", "; ", StringComparison.Ordinal);
        fixture.Baseline[scribePath] = scribeSource;
        fixture.ForkPoint[scribePath] = scribeSource;

        var completed = Execute(fixture, RuleFixture.RingPath, scribePath);

        Assert.Contains(RuleId.CreateKnown(19), completed.ExecutedRules);
        AssertFinding(completed, 19, "unledgered anomaly", artifactPath);
    }

    [Theory]
    [InlineData("tools/StrataLint.Engine/Rules/RepositoryRules.Helpers.cs")]
    [InlineData("tools/Trureturing.Truth/YamlSubsetParser.cs")]
    public void Sl019ReplaysWhenGrammarOrParserChangesAlongsideTaskPreservingLeanEdit(
        string dependencyPath)
    {
        const string artifactPath = "Evidence/D5/S0/Carrier/Result.run.yaml";
        const string task = "/-- TASK D5-T0097\n    historical task. -/\n";
        const string anomaly = "anomaly: fixture drift\ncase_id: D5-T0098\n";
        var fixture = new RuleFixture();
        fixture.Baseline[RuleFixture.RingPath] += task;
        fixture.ForkPoint[RuleFixture.RingPath] += task;
        fixture.Files[RuleFixture.RingPath] = fixture.Baseline[RuleFixture.RingPath]
            .Replace("Nat := 0", "Nat := 1", StringComparison.Ordinal);
        fixture.Files[artifactPath] = anomaly;
        fixture.Baseline[artifactPath] = anomaly;
        fixture.ForkPoint[artifactPath] = anomaly;

        var changes = RawChangeSet.Create([RuleFixture.RingPath, dependencyPath]);
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(changes))).Capability;

        Assert.Contains(RuleId.CreateKnown(19), completed.ExecutedRules);
        AssertFinding(completed, 19, "unledgered anomaly", artifactPath);
    }

    [Theory]
    [InlineData("fail{\"key\":\"value\"}ure")]
    [InlineData("fail{}ure")]
    [InlineData("fail[]ure")]
    public void Sl019EmbeddedJsonPreservesOpaqueFragmentBoundaries(string payload)
    {
        const string path = "Evidence/D5/S0/Carrier/Serialized.run.json";
        var fixture = new RuleFixture();
        SetHistorical(
            fixture,
            path,
            JsonSerializer.Serialize(new { payload }) + "\n");

        var completed = Execute(
            fixture,
            "tools/StrataLint.Engine/Rules/RepositoryRules.StructuredScan.cs");

        AssertNoFinding(completed, 19, "unknown anomaly-bearing schema", path);
    }

    [Fact]
    [BaseFactScopeProbe(20)]
    public void Sl020HistoricalAxiomFindingSurvivesUnrelatedLeanDelta()
    {
        AssertThreeFaces(
            () => AxiomHistory(),
            20,
            "unregistered transitive axiom closure",
            RuleFixture.RingPath,
            "tools/StrataLint.Engine/Rules/RepositoryRules.Admission.cs");

        const string dependencyPath = "D5/S0/Carrier/AxiomDependency.lean";
        var dependencyDelta = AxiomHistory(dependencyPath);
        AssertFinding(
            Execute(dependencyDelta, dependencyPath),
            20,
            "unregistered transitive axiom closure",
            RuleFixture.RingPath);

        var bothDelta = AxiomHistory(dependencyPath);
        AssertFinding(
            Execute(bothDelta, RuleFixture.RingPath, dependencyPath),
            20,
            "unregistered transitive axiom closure",
            RuleFixture.RingPath);
    }

    private static void AssertThreeFaces(
        Func<RuleFixture> fixtureFactory,
        int ruleNumber,
        string message,
        string findingPath,
        string implementationPath)
    {
        var unrelated = fixtureFactory();
        AssertNoFinding(
            Execute(unrelated, UnrelatedLeanPath),
            ruleNumber,
            message,
            findingPath);

        var changed = fixtureFactory();
        AssertFinding(
            Execute(changed, findingPath),
            ruleNumber,
            message,
            findingPath);

        var implementation = fixtureFactory();
        AssertFinding(
            Execute(implementation, implementationPath),
            ruleNumber,
            message,
            findingPath);
    }

    private static RuleFixture ImportHistory()
    {
        var fixture = new RuleFixture();
        fixture.AddUpwardImport();
        SetCurrentAdditionsHistorical(fixture);
        return fixture;
    }

    private static RuleFixture SorryHistory(string? dependencyPath = null)
    {
        var fixture = new RuleFixture();
        fixture.SetRingDeclaration("historicalSorry", "theorem", "sorryAx");
        if (dependencyPath is not null)
        {
            AddHistoricalLeanFile(fixture, dependencyPath, "D5/S0/Carrier/SorryDependency");
            fixture.Reports[RuleFixture.RingPath] = new LeanFileReport(
                ["D5.S0.Carrier.SorryDependency"],
                [new LeanDeclaration("historicalSorry", "theorem", "False", ["sorryAx"])]);
        }

        return fixture;
    }

    private static RuleFixture GeneralityHistory()
    {
        var fixture = new RuleFixture();
        fixture.AddInstanceImport();
        SetCurrentAdditionsHistorical(fixture);
        return fixture;
    }

    private static RuleFixture DomainHistory()
    {
        var fixture = new RuleFixture();
        fixture.AddUnknownDomain();
        SetCurrentAdditionsHistorical(fixture);
        return fixture;
    }

    private static RuleFixture AnchorHistory(string? dependencyPath = null)
    {
        const string target = "Mathlib.Data.Nat.Fib.Zeckendorf";
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath].Replace(
            "anchors: []",
            $"anchors: [mathlib/module/{target}]",
            StringComparison.Ordinal);
        SetHistorical(fixture, RuleFixture.RingPath, fixture.Files[RuleFixture.RingPath]);
        if (dependencyPath is not null)
        {
            AddHistoricalLeanFile(fixture, dependencyPath, "D5/S0/Carrier/AnchorDependency");
            fixture.Reports[RuleFixture.RingPath] = new LeanFileReport(
                ["D5.S0.Carrier.AnchorDependency"],
                ImmutableArray<LeanDeclaration>.Empty);
        }

        return fixture;
    }

    private static RuleFixture ValuesPathHistory(string path)
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, path, "{}\n");
        return fixture;
    }

    private static RuleFixture AnomalyHistory(string path)
    {
        var fixture = new RuleFixture();
        SetHistorical(fixture, path, "{\"kind\":\"fixture-anomaly\",\"state\":\"invalid\"}\n");
        return fixture;
    }

    private static void AddHistoricalTask(RuleFixture fixture)
    {
        const string task = "/-- TASK D5-T0099\n    historical task. -/\n";
        fixture.Baseline[RuleFixture.ValuesBindingPath] += task;
        fixture.ForkPoint[RuleFixture.ValuesBindingPath] += task;
    }

    private static RuleFixture AxiomHistory(string? dependencyPath = null)
    {
        var fixture = new RuleFixture();
        var imports = ImmutableArray<string>.Empty;
        if (dependencyPath is not null)
        {
            AddHistoricalLeanFile(fixture, dependencyPath, "D5/S0/Carrier/AxiomDependency");
            imports = ["D5.S0.Carrier.AxiomDependency"];
        }

        fixture.Reports[RuleFixture.RingPath] = new LeanFileReport(
            imports,
            [new LeanDeclaration("historicalAxiom", "theorem", "True", ["Fixture.badAxiom"])]);
        return fixture;
    }

    private static void AddHistoricalLeanFile(RuleFixture fixture, string path, string gid)
    {
        SetHistorical(fixture, path, Header(gid) + "def dependency : Nat := 0\n");
        fixture.Reports[path] = new LeanFileReport([], []);
    }

    private static void SetCurrentAdditionsHistorical(RuleFixture fixture)
    {
        foreach (var (path, text) in fixture.Files)
        {
            fixture.Baseline.TryAdd(path, text);
            fixture.ForkPoint.TryAdd(path, text);
        }
    }

    private static void SetHistorical(RuleFixture fixture, string path, string text)
    {
        fixture.Files[path] = text;
        fixture.Baseline[path] = text;
        fixture.ForkPoint[path] = text;
    }

    private static CompletedRuleSet Execute(RuleFixture fixture, params string[] changedPaths) =>
        Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create(changedPaths)))).Capability;

    private static void AssertFinding(
        CompletedRuleSet completed,
        int ruleNumber,
        string message,
        string path) =>
        Assert.Contains(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(ruleNumber)
            && diagnostic.Path == path
            && diagnostic.Message.Contains(message, StringComparison.Ordinal));

    private static void AssertNoFinding(
        CompletedRuleSet completed,
        int ruleNumber,
        string message,
        string path) =>
        Assert.DoesNotContain(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(ruleNumber)
            && diagnostic.Path == path
            && diagnostic.Message.Contains(message, StringComparison.Ordinal));

    private static string Header(string gid) => $"""
        /- GID: {gid}
           generality: G
           mirror-B: none(waiver:test-fixture)
           mirror-E: none(waiver:test-fixture)
           anchors: []
           digest: R15 scope fixture. -/
        """;
}
