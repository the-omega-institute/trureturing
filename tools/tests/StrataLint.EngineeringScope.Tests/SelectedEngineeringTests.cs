using System.Text.Json.Nodes;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class SelectedEngineeringTests
{
    [Fact]
    public void DeclaredRepositoryUnitRunsWithoutUnselectedFixtureProjects()
    {
        using var fixture = new SelectedEngineeringFixture();
        var calls = new List<string>();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (project, results) =>
        {
            calls.Add(project);
            fixture.Trx(results);
            return 0;
        }, TextWriter.Null, fixture.Build));
        Assert.Equal([ResourceRouteTests.ResourceFixture.Foo], calls);
        var accepted = CommonExecutionEvidence.ValidateTests(fixture.Root);
        Assert.Equal(ResourceRouteTests.ResourceFixture.Foo, Assert.Single(accepted.Projects).Project);
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root,
            [ResourceRouteTests.ResourceFixture.Bar]));
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("duplicate")]
    [InlineData("unselected")]
    [InlineData("candidate")]
    [InlineData("round")]
    [InlineData("trx")]
    public void SelectedUnitEvidenceRemainsBoundAndComplete(string defect)
    {
        using var fixture = new SelectedEngineeringFixture();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) =>
        {
            fixture.Trx(results);
            return 0;
        }, TextWriter.Null, fixture.Build));
        var record = CommonExecutionEvidence.Read<TestExecutionRecord>(fixture.Root, CommonExecutionEvidence.TestsPath);
        var first = Assert.Single(record.Projects);
        switch (defect)
        {
            case "missing": record = record with { Projects = [] }; break;
            case "duplicate": record = record with { Projects = [first, first] }; break;
            case "unselected": record = record with { Projects = [first with { Project = ResourceRouteTests.ResourceFixture.Bar }] }; break;
            case "candidate": record = record with { Candidate = new string('a', 64) }; break;
            case "round": record = record with { Round = "different-round" }; break;
            case "trx": File.Delete(Path.Combine(fixture.Root, first.Results, "execution.trx")); break;
        }
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.TestsPath, record);
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

    [Theory]
    [InlineData("passed", 0)]
    [InlineData("failed", 1)]
    [InlineData("missing-trx", 1)]
    public void RepositoryStageRunsRealSelectedTestsAndDoesNotProduceEmptyChecks(string scenario, int expected)
    {
        using var fixture = new SelectedEngineeringFixture();
        var result = fixture.Run(scenario);
        Assert.True(result.Exit == expected, result.Text);
        Assert.Equal(["test"], File.ReadAllLines(Path.Combine(fixture.Root, "build/selected-events")));
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.ChecksPath("engineering"))));
        if (expected == 0)
        {
            var stage = CommonExecutionEvidence.ValidateEngineering(fixture.Root);
            Assert.Equal(["tests"], stage.Steps.Select(step => step.Name));
            Assert.DoesNotContain(stage.Materials, material => material.Path == CommonExecutionEvidence.ChecksPath("engineering"));
            var summary = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/engineering-result.json")))!;
            Assert.Empty(summary["not_executed"]!.AsArray());
            Assert.Equal(new[] { "selftest-pair", "capability-proof", "banned-api-proof" },
                summary["not_required"]!.AsArray().Select(item => item!.ToString()));
        }
        else Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.EngineeringPath)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SelectedTestSeedIsReusableAndCorruptionRunsTheProjectAgain(bool corrupt)
    {
        using var fixture = new SelectedEngineeringFixture();
        var first = fixture.Run("passed", "automatic");
        Assert.True(first.Exit == 0, first.Text);
        var tests = CommonExecutionEvidence.ValidateTests(fixture.Root);
        Assert.Single(tests.Projects);
        Assert.Empty(CommonExecutionEvidence.ValidateCheckSeedBundle(fixture.Root, "engineering").Units);
        if (corrupt)
            File.WriteAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.TestSeedPath, tests.Materials[0].Path), "invalid optional seed");
        var next = fixture.Run("passed");
        Assert.True(next.Exit == 0, next.Text);
        Assert.Equal(corrupt ? 2 : 1, File.ReadAllLines(Path.Combine(fixture.Root, "build/selected-events")).Length);
        Assert.Equal(corrupt ? "executed" : "reused", Assert.Single(CommonExecutionEvidence.ValidateTests(fixture.Root).Projects).Status);
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.ChecksPath("engineering"))));
    }

    [Fact]
    public void TestsOnlyEngineeringPacksOptionalSeedWithoutCheckExecutionEvidence()
    {
        using var fixture = new SelectedEngineeringFixture();
        var executed = fixture.Run("passed");
        Assert.True(executed.Exit == 0, executed.Text);
        var ordinary = Path.Combine(fixture.Root, "build/engineering.tgz");
        var seed = Path.Combine(fixture.Root, "build/engineering-seed.tgz");
        Assert.Equal(0, CiTransport.Run(["transport-pack", "--repository", fixture.Root, "--stage", "engineering",
            "--commit", fixture.Commit, "--run-id", "1", "--run-attempt", "1", "--archive", ordinary, "--seed-archive", seed], TextWriter.Null));
        Assert.True(File.Exists(ordinary));
        Assert.True(File.Exists(seed));
        var paths = File.ReadAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.BundleListPath("engineering-seed"))).Split('\0');
        Assert.Contains(CommonExecutionEvidence.TestSeedPath + "/tests.json", paths);
        var tests = CommonExecutionEvidence.ValidateTests(fixture.Root);
        foreach (var material in tests.Materials) Assert.Contains(CommonExecutionEvidence.TestSeedPath + "/" + material.Path, paths);
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.ChecksPath("engineering"))));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SelectedRunPreservesUnselectedOptionalProjectSeedForLaterFullEngineering(bool corrupt)
    {
        using var fixture = new SelectedEngineeringFixture();
        var first = fixture.Run("passed", "automatic");
        Assert.True(first.Exit == 0, first.Text);
        fixture.AddUnselectedTestSeed();
        if (corrupt)
        {
            var seed = Path.Combine(fixture.Root, CommonExecutionEvidence.TestSeedPath);
            var previous = CommonExecutionEvidence.Read<TestExecutionRecord>(seed, "tests.json");
            var unselected = previous.Projects.Single(project => project.Project == ResourceRouteTests.ResourceFixture.Bar);
            File.WriteAllText(Path.Combine(seed, unselected.Results, "execution.trx"), "invalid unselected cache");
        }
        var next = fixture.Run("passed", "automatic");
        Assert.True(next.Exit == 0, next.Text);
        Assert.Single(CommonExecutionEvidence.ValidateTests(fixture.Root).Projects);
        Assert.Equal(new[] { "test" }, File.ReadAllLines(Path.Combine(fixture.Root, "build/selected-events")));
        var calls = new List<string>();
        Assert.Equal(0, fixture.RunFullTests(calls));
        Assert.Equal(corrupt ? new[] { ResourceRouteTests.ResourceFixture.Bar } : [], calls);
    }

    [Theory]
    [InlineData("projects", false)]
    [InlineData("projects", true)]
    [InlineData("materials", false)]
    [InlineData("materials", true)]
    public void MalformedRetainedRowsDoNotPreventSavingAcceptedTests(string field, bool replace)
    {
        using var fixture = new SelectedEngineeringFixture();
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) =>
        {
            fixture.Trx(results);
            return 0;
        }, TextWriter.Null, fixture.Build));
        const string log = "build/ci/selected-tests.log";
        File.WriteAllText(Path.Combine(fixture.Root, log), "selected tests passed\n");
        CommonExecutionEvidence.SealEngineering(fixture.Root, fixture.Build, [new StageStep("tests", 0, 0, "executed", log)]);
        fixture.AddUnselectedTestSeed();
        var seed = Path.Combine(fixture.Root, CommonExecutionEvidence.TestSeedPath);
        var previous = CommonExecutionEvidence.Read<TestExecutionRecord>(seed, "tests.json");
        var unselected = previous.Projects.Single(project => project.Project == ResourceRouteTests.ResourceFixture.Bar);
        var path = Path.Combine(seed, "tests.json");
        var document = JsonNode.Parse(File.ReadAllText(path))!;
        var rows = document[field]!.AsArray();
        if (replace)
        {
            var row = rows.Single(row => field == "projects"
                ? row!["project"]!.ToString() == unselected.Project
                : row!["path"]!.ToString().StartsWith(unselected.Results + "/", StringComparison.Ordinal));
            rows[rows.IndexOf(row)] = null;
        }
        else rows.Add((JsonNode?)null);
        File.WriteAllText(path, document.ToJsonString());

        using var output = new StringWriter();
        Assert.True(CommonExecutionEvidence.ExportTestSeed(fixture.Root, output), output.ToString());
        Assert.Contains("ENGINEERING_TEST_SEED_SAVED", output.ToString());
        var calls = new List<string>();
        Assert.Equal(0, fixture.RunFullTests(calls));
        Assert.Equal(replace ? new[] { ResourceRouteTests.ResourceFixture.Bar } : [], calls);
    }
}
