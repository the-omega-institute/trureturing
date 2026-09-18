using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

internal sealed class SelectedEngineeringFixture : IDisposable
{
    private readonly ResourceRouteTests.ResourceFixture fixture = new(["filemap"]);
    internal string Root => fixture.Root;
    internal string Commit => fixture.Commit;
    internal CommonStageRecord Build { get; }

    internal SelectedEngineeringFixture()
    {
        var mapping = JsonNode.Parse(File.ReadAllText(Path.Combine(Root, "Meta/ci-resources.json")))!;
        var selected = mapping["resources"]!.AsArray().Single(row => row!["id"]!.ToString() == "filemap")!;
        selected["id"] = "repository";
        selected["checks"] = new JsonArray();
        selected["steps"] = new JsonArray();
        fixture.Write("Meta/ci-resources.json", mapping.ToJsonString());
        var filemap = File.ReadAllText(Path.Combine(Root, "Meta/FILEMAP.toml")).Replace("\"filemap\"", "\"repository\"", StringComparison.Ordinal);
        filemap = string.Join('\n', filemap.Split('\n').Select(line => line.Contains("id = \"repository\"", StringComparison.Ordinal)
            ? line.Replace("stage = \"current\"", "stage = \"engineering\"", StringComparison.Ordinal) : line));
        var resourceRows = new Queue<string>(filemap.Split('\n').Where(line => line.StartsWith("  { id =", StringComparison.Ordinal)).Order(StringComparer.Ordinal));
        filemap = string.Join('\n', filemap.Split('\n').Select(line => line.StartsWith("  { id =", StringComparison.Ordinal) ? resourceRows.Dequeue() : line));
        fixture.Write("Meta/FILEMAP.toml", filemap);
        fixture.Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
            new EngineeringProjectFixture(ResourceRouteTests.ResourceFixture.Foo, "Foo", "cross-cutting-test", true, ["tools/Foo/Program.cs"]),
            new EngineeringProjectFixture(ResourceRouteTests.ResourceFixture.Bar, "Bar", "cross-cutting-test", true, ["tools/Bar/Program.cs"])));
        fixture.CommitPlan();
        var plan = ResourceExecutionPlan.Load(Root, fixture.Plan, fixture.Changes)!;
        const string assembly = "build/ci/fixture-bin/Foo.dll";
        fixture.Write(assembly, "synthetic assembly\n");
        fixture.Write("build/ci/fixture-build.log", "successful build\n");
        CommonExecutionEvidence.Write(Root, CommonBuildOutputs.TestsPath,
            new[] { new BuiltTestProject(ResourceRouteTests.ResourceFixture.Foo, assembly) });
        Build = CommonExecutionEvidence.SealBuild(Root, CommonExecutionEvidence.Candidate(Root),
            [assembly, CommonBuildOutputs.TestsPath],
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", "build/ci/fixture-build.log")).ToArray(),
            plan.Projects, plan.Retain(Root));
    }

    internal void Trx(string directory, string outcome = "Passed", string assembly = "Foo")
    {
        Directory.CreateDirectory(directory);
        File.WriteAllText(Path.Combine(directory, "execution.trx"), $$"""
            <TestRun><Results><UnitTestResult testId="one" testName="Fixture.Runs" outcome="{{outcome}}" /></Results>
            <TestDefinitions><UnitTest id="one" storage="{{assembly}}.dll"><TestMethod className="Fixture" name="Runs" /></UnitTest></TestDefinitions>
            <ResultSummary outcome="{{(outcome == "Passed" ? "Completed" : "Failed")}}"><Counters executed="1" passed="{{(outcome == "Passed" ? 1 : 0)}}" failed="{{(outcome == "Failed" ? 1 : 0)}}" /></ResultSummary></TestRun>
            """);
    }

    internal void AddUnselectedTestSeed()
    {
        var seed = Path.Combine(Root, CommonExecutionEvidence.TestSeedPath);
        var selected = CommonExecutionEvidence.Read<TestExecutionRecord>(Root, CommonExecutionEvidence.TestsPath);
        var inventory = File.ReadAllBytes(Path.Combine(Root, CommonBuildOutputs.TestsPath));
        Assert.Equal(0, RunFullTests([]));
        var record = CommonExecutionEvidence.ValidateTests(Root);
        foreach (var material in record.Materials)
        {
            var destination = Path.Combine(seed, material.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(Path.Combine(Root, material.Path), destination, overwrite: true);
        }
        CommonExecutionEvidence.Write(seed, "tests.json", record);
        CommonExecutionEvidence.Write(Root, CommonExecutionEvidence.TestsPath, selected);
        File.WriteAllBytes(Path.Combine(Root, CommonBuildOutputs.TestsPath), inventory);
        CommonExecutionEvidence.Write(Root, CommonExecutionEvidence.BuildPath, Build);
    }

    internal int RunFullTests(List<string> calls)
    {
        const string second = "build/ci/fixture-bin/Bar.dll";
        fixture.Write(second, "synthetic Bar assembly\n");
        CommonExecutionEvidence.Write(Root, CommonBuildOutputs.TestsPath, new[] {
            new BuiltTestProject(ResourceRouteTests.ResourceFixture.Foo, "build/ci/fixture-bin/Foo.dll"),
            new BuiltTestProject(ResourceRouteTests.ResourceFixture.Bar, second) });
        var build = CommonExecutionEvidence.SealBuild(Root, CommonExecutionEvidence.Candidate(Root),
            ["build/ci/fixture-bin/Foo.dll", second, CommonBuildOutputs.TestsPath], Build.Steps);
        return Program.RunCurrentTests(Root, (project, directory) =>
        {
            calls.Add(project);
            Trx(directory, assembly: Path.GetFileNameWithoutExtension(project));
            return 0;
        }, TextWriter.Null, build);
    }

    internal (int Exit, string Text) Run(string scenario, string export = "deferred")
    {
        Trx(Path.Combine(Root, "build/selected-trx"), scenario == "failed" ? "Failed" : "Passed");
        var scope = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        fixture.Executable("build/selected-bin/dotnet", """
            if [[ "$1" == *.EngineeringScope.dll ]]; then shift; exec "$SELECTED_SCOPE" "$@"; fi
            [[ "$1" == test ]] || { printf 'unexpected selected process: %s\n' "$*"; exit 97; }
            echo test >> build/selected-events
            while [[ "$1" != --results-directory ]]; do shift; done
            mkdir -p "$2"
            [[ "$SELECTED_SCENARIO" == missing-trx ]] || cp build/selected-trx/execution.trx "$2/execution.trx"
            [[ "$SELECTED_SCENARIO" != failed ]]
            """);
        return SharedBuildContractTests.Process(Root, scope,
            ["engineering", "--repository", Root, "--build-round", Build.Round,
                "--plan", fixture.Plan, "--changes", fixture.Changes, "--seed-export", export],
            new Dictionary<string, string>
            {
                ["PATH"] = Path.Combine(Root, "build/selected-bin") + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
                ["SELECTED_SCOPE"] = scope,
                ["SELECTED_SCENARIO"] = scenario,
            });
    }

    public void Dispose() => fixture.Dispose();
}
