using StrataLint.Cli;

namespace StrataLint.ArchitectureTests;

public sealed class TestSelectionPolicyTests
{
    private const string ScribeDefinition = "Blueprint/D5/S0/Carrier/Ring.scribe.cs";
    private const string ScribeProjection = "Blueprint/D5/S0/Carrier/Ring.md";

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
    public void PullRequestScribeDefinitionsOnlySkipsEngineTests()
    {
        var selected = TestSelectionPolicy.Select(
            TestSelectionEvent.PullRequest,
            [ScribeDefinition]);

        Assert.Equal(
            [TestSelectionPolicy.ArchitectureTests, TestSelectionPolicy.ScribeTests],
            selected);
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
    public void PullRequestMixedChangesRunFullSuiteInsteadOfPartiallyMatching()
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
}
