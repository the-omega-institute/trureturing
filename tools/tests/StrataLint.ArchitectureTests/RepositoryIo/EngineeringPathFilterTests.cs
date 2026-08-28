namespace StrataLint.ArchitectureTests;

public sealed class EngineeringPathFilterTests
{
    [Fact]
    public void ToolsChangePlansFullAndExecutesTheWholeSolution()
    {
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["tools/StrataLint.Engine/RepositoryIo/EngineeringTestPlanPolicy.cs"],
            EmptyMap(),
            compileAffectedTestProjects: EmptyProjects());
        var calls = new List<EngineeringTestInvocation>();

        var exitCode = EngineeringTestExecutor.Execute(plan, invocation =>
        {
            calls.Add(invocation);
            return 0;
        });

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.Equal(0, exitCode);
        Assert.Equal("tools/StrataLint.sln", Assert.Single(calls).Target);
    }

    [Fact]
    public void DisjointContentExecutesUnknownTargetButNotSyntheticRuleEngineTarget()
    {
        var map = Map(
            new ScribeTestMethod(
                "tools/tests/StrataLint.Tests",
                "tools/tests/StrataLint.Tests/ProductionEnvironmentTests.cs",
                "ProductionEnvironmentTests.ReadsRepository",
                [],
                [TestMapUnknownReason.VariablePath]),
            new ScribeTestMethod(
                "tools/tests/StrataLint.Tests",
                "tools/tests/StrataLint.Tests/Rules/RuleEngineTests.cs",
                "RuleEngineTests.UsesSyntheticFixture",
                [],
                []));
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["docs/develop/selector-negative.md"],
            map,
            compileAffectedTestProjects: EmptyProjects());
        var calls = new List<EngineeringTestInvocation>();

        var exitCode = EngineeringTestExecutor.Execute(plan, invocation =>
        {
            calls.Add(invocation);
            return 0;
        });

        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Contains(plan.Tests, test => test.Id.Contains("ProductionEnvironmentTests", StringComparison.Ordinal));
        Assert.DoesNotContain(plan.Tests, test => test.Id.Contains("RuleEngineTests", StringComparison.Ordinal));
        Assert.Equal(0, exitCode);
        var call = Assert.Single(calls);
        Assert.Equal("tools/StrataLint.sln", call.Target);
        Assert.Contains("ProductionEnvironmentTests.ReadsRepository", call.Filter, StringComparison.Ordinal);
        Assert.DoesNotContain("RuleEngineTests", call.Filter, StringComparison.Ordinal);
    }

    [Fact]
    public void NoAffectedOrUnknownTargetsPlansNoneAndExecutesNothing()
    {
        var map = Map(new ScribeTestMethod(
            "tools/tests/StrataLint.Tests",
            "tools/tests/StrataLint.Tests/Rules/RuleEngineTests.cs",
            "RuleEngineTests.UsesSyntheticFixture",
            [],
            []));
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["docs/develop/selector-negative.md"],
            map,
            compileAffectedTestProjects: EmptyProjects());
        var calls = new List<EngineeringTestInvocation>();

        var exitCode = EngineeringTestExecutor.Execute(plan, invocation =>
        {
            calls.Add(invocation);
            return 0;
        });

        Assert.Equal(EngineeringTestPlanKind.None, plan.Kind);
        Assert.Equal(0, exitCode);
        Assert.Empty(calls);
    }

    [Fact]
    public void ProjectAttributionFailurePlansFull()
    {
        var map = EmptyMap() with
        {
            OrphanManagedSourcePaths = ["tools/tests/Unknown/NewTests.cs"],
        };

        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["Meta/Digestion/example.json"],
            map,
            compileAffectedTestProjects: EmptyProjects());

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.Contains("project attribution", plan.Reason, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SelectedExecutionFailureFallsBackToFull(bool throws)
    {
        var map = Map(new ScribeTestMethod(
            "tools/tests/StrataLint.Tests",
            "tools/tests/StrataLint.Tests/ProductionEnvironmentTests.cs",
            "ProductionEnvironmentTests.ReadsRepository",
            [],
            [TestMapUnknownReason.VariablePath]));
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["Meta/Digestion/example.json"],
            map,
            compileAffectedTestProjects: EmptyProjects());
        var calls = new List<EngineeringTestInvocation>();

        var exitCode = EngineeringTestExecutor.Execute(plan, invocation =>
        {
            calls.Add(invocation);
            if (throws && calls.Count == 1) throw new InvalidOperationException("selected invocation failed");
            return calls.Count == 1 ? 1 : 0;
        });

        Assert.Equal(0, exitCode);
        Assert.Equal(2, calls.Count);
        Assert.NotNull(calls[0].Filter);
        Assert.Equal("tools/StrataLint.sln", calls[1].Target);
        Assert.Null(calls[1].Filter);
    }

    [Fact]
    public void Pr2343ReplayExecutesBlueprintConsumers()
    {
        string[] changedPaths =
        [
            "Blueprint/D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact.md",
            "Blueprint/D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact.scribe.cs",
            "D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact.lean",
            "Golden/Frozen/accepted/2d08439d70b4a41aa0a08eec6b47bdb25c3bc7199added3404b63ec68deaf5a4.json",
            "Meta/Digestion/formalizations/cone-residual-1013db8f686811f4043dadb9867335e028412bfb1aca2ef31229e238fd2db820.v1.json",
        ];
        var plan = EngineeringTestPlanDeriver.DeriveRepository(
            RepositoryLayout.FindRoot(),
            changedPaths);
        var calls = new List<EngineeringTestInvocation>();

        var exitCode = EngineeringTestExecutor.Execute(plan, invocation =>
        {
            calls.Add(invocation);
            return 0;
        });

        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Contains(plan.Tests, static test =>
            test.Reason == EngineeringSelectedTestReason.CompiledInput
            && test.ProjectPath.EndsWith("StrataLint.Scribe.Tests.csproj", StringComparison.Ordinal));
        Assert.Equal(0, exitCode);
        var call = Assert.Single(calls);
        var consumer = plan.Tests.First(static test =>
            test.Reason == EngineeringSelectedTestReason.CompiledInput
            && test.ProjectPath.EndsWith("StrataLint.Scribe.Tests.csproj", StringComparison.Ordinal));
        Assert.Equal("tools/StrataLint.sln", call.Target);
        Assert.Contains(consumer.Id, call.Filter, StringComparison.Ordinal);
    }

    private static ScribeTestMap EmptyMap() => Map();

    private static IReadOnlySet<string> EmptyProjects() => new HashSet<string>(StringComparer.Ordinal);

    private static ScribeTestMap Map(params ScribeTestMethod[] methods) => new(
        methods,
        [],
        [],
        [],
        methods.ToDictionary(
            static method => method.SourcePath,
            static method => method.PartitionKey + "/" + Path.GetFileName(method.PartitionKey) + ".csproj",
            StringComparer.Ordinal),
        []);
}
