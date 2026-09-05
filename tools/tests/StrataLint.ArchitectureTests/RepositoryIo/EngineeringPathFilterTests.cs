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
    private const string CandidateAddedProject =
        "tools/tests/StrataLint.Added.Tests/StrataLint.Added.Tests.csproj";
    private const string HeuristicOnlyProject =
        "tools/tests/StrataLint.Heuristic.Tests/StrataLint.Heuristic.Tests.csproj";

    // issue #5516:StrataLint.TestSupport 为 TestScratchFramework 派生 XunitTestFramework
    // 而必须引用 xunit,同时明写 IsTestProject=false。此前 xunit 启发式优先于显式声明,
    // 把它判成测试项目 -> full plan 选中它 -> dotnet test 对它不产 TRX ->
    // ENGINEERING_TEST_EVIDENCE_FAILED,阻塞所有 judge 面 PR。
    [Fact]
    public void FullPlanExcludesXunitReferencingProjectThatDeclaresItselfNonTest()
    {
        var topology = new TestProjectTopologySnapshot(
        [
            SupportProjectDeclaringNonTest(TestSupportProject),
            Project(EngineProject, isTest: false),
            Project(EngineTestsProject, isTest: true, EngineProject),
        ]);

        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(
            ["tools/StrataLint.Engine/Anything.cs"],
            topology,
            topology,
            full: true);

        Assert.DoesNotContain(TestSupportProject, plan.Projects);
        Assert.Contains(EngineTestsProject, plan.Projects);
    }

    // `_ => Ambiguous` 这条分支只在 candidate-added 侧可观测:base 侧的 Ambiguous 被当作
    // 非测试项目静默排除,而 candidate-added 侧 fail-closed 抛 InvalidDataException。
    // 旧判据把 xunit 启发式放在字面量之前,于是「字面量互相冲突 + 引用 xunit」被判成 Test,
    // 这条 fail-closed 路径根本到不了 —— 冲突被静默吞掉,项目被当作测试项目收下。
    [Fact]
    public void CandidateAddedProjectWithConflictingLiteralsFailsClosed()
    {
        var protectedBase = new TestProjectTopologySnapshot(
        [
            Project(EngineProject, isTest: false),
            Project(EngineTestsProject, isTest: true, EngineProject),
        ]);
        var candidate = new TestProjectTopologySnapshot(
        [
            Project(EngineProject, isTest: false),
            Project(EngineTestsProject, isTest: true, EngineProject),
            ConflictingLiteralXunitProject(CandidateAddedProject),
        ]);

        var error = Assert.Throws<InvalidDataException>(() =>
            EngineeringTestPlanPolicy.EvaluateOrdinary(
                ["tools/StrataLint.Engine/Anything.cs"],
                protectedBase,
                candidate,
                full: true));

        Assert.Contains(CandidateAddedProject, error.Message, StringComparison.Ordinal);
    }

    // 放行侧钉子。显式声明优先之后,`[]`(无 IsTestProject 元素)这条分支仍必须回落到
    // xunit 启发式。它在旧判据下同样绿 —— 守的不是本次修复,而是防止日后把回落删成
    // `[] => NonTest`:那会让每一个不写 IsTestProject 的测试项目静默退出计划,
    // 而「计划变空」在放行侧不产生任何红。
    [Fact]
    public void ProjectWithoutLiteralDeclarationIsClassifiedByTheXunitHeuristic()
    {
        var topology = new TestProjectTopologySnapshot(
        [
            Project(EngineProject, isTest: false),
            HeuristicOnlyTestProject(HeuristicOnlyProject),
        ]);

        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(
            ["tools/StrataLint.Engine/Anything.cs"],
            topology,
            topology,
            full: true);

        Assert.Contains(HeuristicOnlyProject, plan.Projects);
    }

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

    private static TestProjectTopologyProject SupportProjectDeclaringNonTest(string path) =>
        new(
            path,
            "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup>"
            + "<IsTestProject>false</IsTestProject></PropertyGroup>"
            + "<ItemGroup><PackageReference Include=\"xunit\" /></ItemGroup></Project>");

    private static TestProjectTopologyProject ConflictingLiteralXunitProject(string path) =>
        new(
            path,
            "<Project Sdk=\"Microsoft.NET.Sdk\">"
            + "<PropertyGroup><IsTestProject>true</IsTestProject></PropertyGroup>"
            + "<PropertyGroup><IsTestProject>false</IsTestProject></PropertyGroup>"
            + "<ItemGroup><PackageReference Include=\"xunit\" /></ItemGroup></Project>");

    private static TestProjectTopologyProject HeuristicOnlyTestProject(string path) =>
        new(
            path,
            "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup /><ItemGroup>"
            + "<PackageReference Include=\"xunit\" /></ItemGroup></Project>");

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
