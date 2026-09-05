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
    private const string ScriptTestsProject =
        "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";
    private const string TestSupportProject =
        "tools/TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj";

    [Fact]
    public void ScribeChangeSelectsBaseReverseTestProjectClosure()
    {
        var topology = Topology(scribeTestsReferenceScribe: true);
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(
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
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(
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
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(
            ["D5/S3/UnownedChange.lean"],
            topology,
            topology);

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.Equal(
            [ArchitectureTestsProject, EngineTestsProject, ScribeTestsProject, ScriptTestsProject],
            plan.Projects.ToArray());
    }

    [Fact]
    public void LiteralFalseXunitProjectIsExcludedFromFullAndFallbackPlans()
    {
        var topology = new TestProjectTopologySnapshot(
        [
            ProjectWithClassifications(TestSupportProject, ["false"], referencesXunit: true),
            ProjectWithClassifications(EngineTestsProject, ["true"], referencesXunit: true),
        ]);

        var full = EngineeringTestPlanPolicy.EvaluateOrdinary(
            [],
            topology,
            topology,
            full: true);
        var fallback = EngineeringTestPlanPolicy.EvaluateOrdinary(
            ["Meta/Digestion/backfill/source/residual-open/atom.yaml"],
            topology,
            topology);

        Assert.Equal(EngineeringTestPlanKind.Full, full.Kind);
        Assert.Equal(EngineeringTestPlanKind.Full, fallback.Kind);
        Assert.Equal([EngineTestsProject], full.Projects.ToArray());
        Assert.Equal([EngineTestsProject], fallback.Projects.ToArray());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LiteralTrueProjectIsSelectedWithOrWithoutXunit(bool referencesXunit)
    {
        var topology = new TestProjectTopologySnapshot(
        [
            ProjectWithClassifications(
                EngineTestsProject,
                ["true"],
                referencesXunit),
        ]);

        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(
            [],
            topology,
            topology,
            full: true);

        Assert.Equal([EngineTestsProject], plan.Projects.ToArray());
    }

    [Fact]
    public void XunitProjectWithoutLiteralIsSelectedByHeuristic()
    {
        var topology = new TestProjectTopologySnapshot(
        [
            ProjectWithClassifications(
                EngineTestsProject,
                [],
                referencesXunit: true),
        ]);

        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(
            [],
            topology,
            topology,
            full: true);

        Assert.Equal([EngineTestsProject], plan.Projects.ToArray());
    }

    [Fact]
    public void ProjectWithoutLiteralOrXunitIsExcluded()
    {
        var topology = new TestProjectTopologySnapshot(
        [
            ProjectWithClassifications(
                EngineProject,
                [],
                referencesXunit: false),
        ]);

        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(
            [],
            topology,
            topology,
            full: true);

        Assert.Empty(plan.Projects);
    }

    [Fact]
    public void CandidateAddedProjectWithConflictingLiteralsFailsClosed()
    {
        var protectedBase = new TestProjectTopologySnapshot([]);
        var candidate = new TestProjectTopologySnapshot(
        [
            ProjectWithClassifications(
                EngineTestsProject,
                ["true", "false"],
                referencesXunit: true),
        ]);

        var error = Assert.Throws<InvalidDataException>(() =>
            EngineeringTestPlanPolicy.EvaluateOrdinary(
                [EngineTestsProject],
                protectedBase,
                candidate));

        Assert.Contains(
            "candidate-added project has no literal IsTestProject classification",
            error.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RealTestSupportProjectIsAbsentFromEveryProducedPlan()
    {
        var topology = RepositoryRules.ReadTrackedProjects(RepositoryLayout.FindRoot());
        var plans = new[]
        {
            EngineeringTestPlanPolicy.EvaluateOrdinary([], topology, topology, full: true),
            EngineeringTestPlanPolicy.EvaluateOrdinary(
                ["Meta/Digestion/backfill/source/residual-open/atom.yaml"],
                topology,
                topology),
            EngineeringTestPlanPolicy.EvaluateOrdinary(
                ["tools/TestSupport/StrataLint.TestSupport/TestProcessRunner.cs"],
                topology,
                topology),
        };

        Assert.All(
            plans,
            plan => Assert.DoesNotContain(TestSupportProject, plan.Projects));
    }

    [Fact]
    public void BlueprintCompileItemChangeSelectsItsConsumerProjectClosure()
    {
        var topology = Topology(
            scribeTestsReferenceScribe: true,
            scribeCompilesBlueprints: true);
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(
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
        var calls = new HashSet<string>(StringComparer.Ordinal);

        var exitCode = EngineeringTestExecutor.Execute(plan, invocation =>
        {
            lock (calls) calls.Add(invocation.ProjectPath);
            return invocation.ProjectPath == ScribeTestsProject ? 17 : 23;
        });

        Assert.Equal(17, exitCode);
        Assert.Equal(
            [ArchitectureTestsProject, ScribeTestsProject],
            calls.Order(StringComparer.Ordinal));
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
        Project(ScriptTestsProject, isTest: true, EngineProject),
        Project(
            ArchitectureTestsProject,
            isTest: true,
            ScribeTestsProject,
            EngineTestsProject),
    ]);

    private static TestProjectTopologyProject Project(
        string path,
        bool isTest,
        params string[] references) =>
        ProjectWithClassifications(
            path,
            isTest ? ["true"] : [],
            referencesXunit: false,
            references);

    private static TestProjectTopologyProject ProjectWithClassifications(
        string path,
        IReadOnlyList<string> classifications,
        bool referencesXunit,
        params string[] references)
    {
        var directory = Path.GetDirectoryName(path)!;
        var projectReferences = string.Join(
            "",
            references.Select(reference =>
                $"<ProjectReference Include=\"{Path.GetRelativePath(directory, reference).Replace('\\', '/')}\" />"));
        var testProperties = string.Join(
            "",
            classifications.Select(value => $"<IsTestProject>{value}</IsTestProject>"));
        var xunitReference = referencesXunit
            ? "<PackageReference Include=\"xunit\" />"
            : "";
        return new TestProjectTopologyProject(
            path,
            $"<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>{testProperties}</PropertyGroup>"
            + $"<ItemGroup>{projectReferences}{xunitReference}</ItemGroup></Project>");
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
