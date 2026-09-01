namespace StrataLint.ArchitectureTests;

public sealed class EngineeringPathFilterTests
{
    private const string ScribeProject =
        "tools/StrataLint.Scribe/StrataLint.Scribe.csproj";
    private const string EngineProject =
        "tools/StrataLint.Engine/StrataLint.Engine.csproj";
    private const string ScribeTestsProject =
        "tools/tests/StrataLint.Scribe.Tests/StrataLint.Scribe.Tests.csproj";
    private const string EngineTestsProject =
        "tools/tests/StrataLint.Engine.Tests/StrataLint.Engine.Tests.csproj";
    private const string ArchitectureTestsProject =
        "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj";

    [Fact]
    public void ScribeChangeSelectsBaseReverseTestProjectClosure()
    {
        var topology = Topology(scribeTestsReferenceScribe: true);
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["tools/StrataLint.Scribe/DocumentEmitter.cs"],
            topology,
            topology);

        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Equal(
            [ArchitectureTestsProject, ScribeTestsProject],
            plan.Projects.ToArray());
    }

    [Fact]
    public void TestProjectChangeSelectsItselfAndItsBaseReverseDependents()
    {
        var topology = Topology(scribeTestsReferenceScribe: true);
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["tools/tests/StrataLint.Engine.Tests/EngineTests.cs"],
            topology,
            topology);

        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Equal(
            [ArchitectureTestsProject, EngineTestsProject],
            plan.Projects.ToArray());
    }

    [Fact]
    public void UnownedChangedPathSelectsAllBaseTestProjects()
    {
        var topology = Topology(scribeTestsReferenceScribe: true);
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["D5/S3/UnownedChange.lean"],
            topology,
            topology);

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.Equal(
            [ArchitectureTestsProject, EngineTestsProject, ScribeTestsProject],
            plan.Projects.ToArray());
    }

    [Fact]
    public void BlueprintCompileItemChangeSelectsItsConsumerProjectClosure()
    {
        var topology = Topology(
            scribeTestsReferenceScribe: true,
            scribeCompilesBlueprints: true);
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["Blueprint/D5/S3/NewDefinition.scribe.cs"],
            topology,
            topology);

        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Equal(
            [ArchitectureTestsProject, ScribeTestsProject],
            plan.Projects.ToArray());
    }

    [Fact]
    public void SelectedProjectFailureDoesNotRetryTheWholeSolution()
    {
        var plan = new EngineeringTestPlan(
            EngineeringTestPlanKind.Selected,
            [],
            [ScribeTestsProject, ArchitectureTestsProject],
            "selected protected-base reverse closure");
        var calls = new List<string>();

        var exitCode = EngineeringTestExecutor.Execute(plan, invocation =>
        {
            calls.Add(invocation.ProjectPath);
            return 17;
        });

        Assert.Equal(17, exitCode);
        Assert.Equal([ScribeTestsProject], calls);
    }

    private static TestProjectTopologySnapshot Topology(
        bool scribeTestsReferenceScribe,
        bool scribeCompilesBlueprints = false) => new(
    [
        scribeCompilesBlueprints
            ? ProjectWithCompile(
                ScribeProject,
                isTest: false,
                "../../Blueprint/**/*.scribe.cs")
            : Project(ScribeProject, isTest: false),
        Project(EngineProject, isTest: false),
        Project(
            ScribeTestsProject,
            isTest: true,
            scribeTestsReferenceScribe ? [ScribeProject] : []),
        Project(EngineTestsProject, isTest: true, EngineProject),
        Project(
            ArchitectureTestsProject,
            isTest: true,
            ScribeTestsProject,
            EngineTestsProject),
    ]);

    private static TestProjectTopologyProject Project(
        string path,
        bool isTest,
        params string[] references)
    {
        var directory = Path.GetDirectoryName(path)!;
        var projectReferences = string.Join(
            "",
            references.Select(reference =>
                $"<ProjectReference Include=\"{Path.GetRelativePath(directory, reference).Replace('\\', '/')}\" />"));
        var testProperty = isTest ? "<IsTestProject>true</IsTestProject>" : "";
        return new TestProjectTopologyProject(
            path,
            $"<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>{testProperty}</PropertyGroup>"
            + $"<ItemGroup>{projectReferences}</ItemGroup></Project>");
    }

    private static TestProjectTopologyProject ProjectWithCompile(
        string path,
        bool isTest,
        string compileInclude)
    {
        var project = Project(path, isTest);
        return project with
        {
            Content = project.Content.Replace(
                "<ItemGroup>",
                $"<ItemGroup><Compile Include=\"{compileInclude}\" />",
                StringComparison.Ordinal),
        };
    }
}
