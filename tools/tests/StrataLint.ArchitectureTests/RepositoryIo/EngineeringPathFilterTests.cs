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
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["tools/StrataLint.Scribe/DocumentEmitter.cs"],
            Topology(scribeTestsReferenceScribe: true));

        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Equal(
            [ArchitectureTestsProject, ScribeTestsProject],
            plan.Projects.ToArray());
    }

    [Fact]
    public void TestProjectChangeSelectsItselfAndItsBaseReverseDependents()
    {
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["tools/tests/StrataLint.Engine.Tests/EngineTests.cs"],
            Topology(scribeTestsReferenceScribe: true));

        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Equal(
            [ArchitectureTestsProject, EngineTestsProject],
            plan.Projects.ToArray());
    }

    [Fact]
    public void UnownedChangedPathSelectsAllBaseTestProjects()
    {
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["D5/S3/UnownedChange.lean"],
            Topology(scribeTestsReferenceScribe: true));

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.Equal(
            [ArchitectureTestsProject, EngineTestsProject, ScribeTestsProject],
            plan.Projects.ToArray());
    }

    [Fact]
    public void CandidateProjectReferenceDeletionCannotShrinkBaseSelection()
    {
        var protectedBasePlan = EngineeringTestPlanPolicy.Evaluate(
            ["tools/StrataLint.Scribe/DocumentEmitter.cs"],
            Topology(scribeTestsReferenceScribe: true));
        var candidateCounterfactual = EngineeringTestPlanPolicy.Evaluate(
            ["tools/StrataLint.Scribe/DocumentEmitter.cs"],
            Topology(scribeTestsReferenceScribe: false));

        Assert.Equal(
            [ArchitectureTestsProject, ScribeTestsProject],
            protectedBasePlan.Projects.ToArray());
        Assert.Equal(EngineeringTestPlanKind.None, candidateCounterfactual.Kind);
        Assert.Empty(candidateCounterfactual.Projects);
    }

    [Fact]
    public void ExecutesEachSelectedProjectWithoutFilterOrSolutionFallback()
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
            return 0;
        });

        Assert.Equal(0, exitCode);
        Assert.Equal([ScribeTestsProject, ArchitectureTestsProject], calls);
        Assert.DoesNotContain(calls, static target =>
            target.EndsWith(".sln", StringComparison.Ordinal));
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

    private static TestProjectTopologySnapshot Topology(bool scribeTestsReferenceScribe) => new(
    [
        Project(ScribeProject, isTest: false),
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
}
