using StrataLint.Cli;

namespace StrataLint.ArchitectureTests;

public sealed class TestSelectionPolicyTests
{
    private const string ScribeDefinition = "Blueprint/D5/S0/Carrier/Ring.scribe.cs";
    private const string ScribeProjection = "Blueprint/D5/S0/Carrier/Ring.md";
    private const string AcceptedPrefix = "Meta/StrataLint/Golden/Frozen/accepted";
    private const string DigestionPrefix = "Meta/Digestion/";
    private const string ScribeProject =
        "Meta/StrataLint/StrataLint.Scribe/StrataLint.Scribe.csproj";

    private static readonly string[] FullSuite =
    [
        TestSelectionPolicy.ArchitectureTests,
        TestSelectionPolicy.EngineTests,
        TestSelectionPolicy.ScribeTests,
    ];

    [Fact]
    public void PullRequestAcceptedEvidenceOnlySkipsEngineAndScribeTests()
    {
        var selected = TestSelectionPolicy.Select(
            TestSelectionEvent.PullRequest,
            ["Meta/StrataLint/Golden/Frozen/accepted/example.json"]);

        Assert.Equal([TestSelectionPolicy.ArchitectureTests], selected);
    }

    [Fact]
    public void PullRequestScribeDefinitionsRunFullSuiteWhileRuleBPremiseIsFalse()
    {
        var selected = TestSelectionPolicy.Select(
            TestSelectionEvent.PullRequest,
            [ScribeDefinition]);

        Assert.Equal(FullSuite, selected);
    }

    [Theory]
    [InlineData("Meta/StrataLint/Golden/Frozen/events.jsonl")]
    [InlineData(ScribeProjection)]
    [InlineData("README.md")]
    public void PullRequestOutsideEitherFamilyRunsFullSuite(string path)
    {
        Assert.Equal(FullSuite, TestSelectionPolicy.Select(TestSelectionEvent.PullRequest, [path]));
    }

    [Fact]
    public void PullRequestMixedChangesIncludingUnknownPathRunFullSuite()
    {
        Assert.Equal(
            FullSuite,
            TestSelectionPolicy.Select(
                TestSelectionEvent.PullRequest,
                [
                    "Meta/StrataLint/Golden/Frozen/accepted/example.json",
                    "README.md",
                ]));
    }

    [Fact]
    public void PullRequestMixedChangesInProvenFamiliesUnionAffectedProjects()
    {
        Assert.Equal(
            [TestSelectionPolicy.ArchitectureTests, TestSelectionPolicy.EngineTests],
            TestSelectionPolicy.Select(
                TestSelectionEvent.PullRequest,
                [
                    "Meta/StrataLint/Golden/Frozen/accepted/example.json",
                    "Meta/Digestion/example.toml",
                ]));
    }

    [Fact]
    public void PullRequestDigestionOnlySkipsScribeTests()
    {
        Assert.Equal(
            [TestSelectionPolicy.ArchitectureTests, TestSelectionPolicy.EngineTests],
            TestSelectionPolicy.Select(
                TestSelectionEvent.PullRequest,
                ["Meta/Digestion/atoms/sha256/example"]));
    }

    [Theory]
    [InlineData("Meta/StrataLint/Golden/Frozen/accepted/example.json")]
    [InlineData(ScribeDefinition)]
    public void DevPushAlwaysRunsFullSuite(string otherwiseSelectablePath)
    {
        Assert.Equal(
            FullSuite,
            TestSelectionPolicy.Select(TestSelectionEvent.DevPush, [otherwiseSelectablePath]));
    }

    [Fact]
    public void EmptyChangeSetFailsClosed()
    {
        Assert.Equal(FullSuite, TestSelectionPolicy.Select(TestSelectionEvent.PullRequest, []));
    }

    [Fact]
    public void UnrecognizedEventFailsClosed()
    {
        Assert.Throws<ArgumentOutOfRangeException>(() =>
            TestSelectionPolicy.Select((TestSelectionEvent)99, ["README.md"]));
    }

    [Fact]
    public void RuleAProjectsDoNotReadAcceptedEvidenceFromTheRepository()
    {
        var root = RepositoryLayout.FindRoot();
        Assert.Empty(TestSelectionSafetyPolicy.InspectProjectSources(
            root, "Meta/StrataLint/StrataLint.Tests", AcceptedPrefix));
        Assert.Empty(TestSelectionSafetyPolicy.InspectProjectSources(
            root, "Meta/StrataLint/StrataLint.Scribe.Tests", AcceptedPrefix));
    }

    [Fact]
    public void DigestionFamilyDoesNotReachScribeTestsThroughRepositoryReads()
    {
        var root = RepositoryLayout.FindRoot();

        Assert.Empty(TestSelectionSafetyPolicy.InspectProjectSources(
            root, "Meta/StrataLint/StrataLint.Scribe.Tests", DigestionPrefix));
    }

    [Fact]
    public void RuleBIsDeferredBecauseEngineTestReferenceClosureContainsScribe()
    {
        var root = RepositoryLayout.FindRoot();
        var closure = TestSelectionSafetyPolicy.ProjectReferenceClosure(Path.Combine(
            root, TestSelectionPolicy.EngineTests));

        Assert.Contains(
            Path.Combine(root, ScribeProject),
            closure);
    }

    [Theory]
    [InlineData("File.ReadAllText(\"Meta/StrataLint/Golden/Frozen/accepted/a.json\");")]
    [InlineData("File.ReadAllText(\"Meta/Digestion/probe.toml\");")]
    [InlineData("const string AcceptedRoot = \"Meta/StrataLint/Golden/Frozen/accepted\"; File.ReadAllText(AcceptedRoot);")]
    [InlineData("Path.Combine(AppContext.BaseDirectory, \"Blueprint/D5/Probe.scribe.cs\");")]
    public void RepositoryReadsAreRejectedAcrossSupportedShapes(string statement)
    {
        var source = "class Probe { void Read() { " + statement + " } }";
        var constants = new HashSet<string>(StringComparer.Ordinal) { "AcceptedRoot" };

        Assert.Single(TestSelectionSafetyPolicy.InspectSource(
            "Probe.cs", source,
            statement.Contains("Blueprint/", StringComparison.Ordinal) ? "Blueprint/"
                : statement.Contains("Meta/Digestion/", StringComparison.Ordinal) ? DigestionPrefix
                : AcceptedPrefix,
            constants));
    }

    [Fact]
    public void TemporaryFixturePathIsRecognizedAsSafe()
    {
        const string source = "class Probe { void Read(TemporaryDirectory repository) { "
            + "File.ReadAllText(Path.Combine(repository.Path, AcceptedRoot)); } }";

        Assert.Empty(TestSelectionSafetyPolicy.InspectSource(
            "Probe.cs",
            source,
            AcceptedPrefix,
            new HashSet<string>(StringComparer.Ordinal) { "AcceptedRoot" }));
    }
}
