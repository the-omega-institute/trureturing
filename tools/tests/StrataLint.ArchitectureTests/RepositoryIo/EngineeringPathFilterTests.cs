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

    [Fact]
    public void BlueprintDefinitionDeltaDoesNotSelectEveryMethodOfTransitiveDependents()
    {
        var changedPaths = new[] { "Blueprint/D5/X/Y.scribe.cs" };
        var compiled = EngineeringCompileInputDeriver.FindAffectedTestProjects(
            ProjectSnapshot(
                ("tools/StrataLint.Scribe/StrataLint.Scribe.csproj", ScribeProject),
                ("tools/tests/Tests/Tests.csproj", TestsProject)),
            changedPaths,
            out var failure);
        var plan = EngineeringTestPlanPolicy.Evaluate(
            changedPaths,
            Map(
                Method("ClosedWithoutBlueprint"),
                Method("DeclaresBlueprint", ["Blueprint"]),
                Method("UnknownRepositoryInput", unknown: true)),
            compiled,
            failure);

        Assert.Null(failure);
        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.DoesNotContain(plan.Tests, static test => test.Id.EndsWith("ClosedWithoutBlueprint", StringComparison.Ordinal));
        Assert.Contains(plan.Tests, static test =>
            test.Id.EndsWith("DeclaresBlueprint", StringComparison.Ordinal)
            && test.Reason == EngineeringSelectedTestReason.DeclaredInput);
        Assert.Contains(plan.Tests, static test =>
            test.Id.EndsWith("UnknownRepositoryInput", StringComparison.Ordinal)
            && test.Reason == EngineeringSelectedTestReason.UnknownInput);
    }

    [Fact]
    public void ScribeEngineSourceDeltaStillSelectsDependentProjectsWholesale()
    {
        var map = Map(Method("ClosedWithoutDeclaredInputs"));
        var fullPlan = EngineeringTestPlanPolicy.Evaluate(
            ["tools/StrataLint.Scribe/Foo.cs"],
            map,
            compileAffectedTestProjects: EmptyProjects());
        var changedPaths = new[] { "Shared/Generated.cs" };
        var compiled = EngineeringCompileInputDeriver.FindAffectedTestProjects(
            ProjectSnapshot(
                ("tools/StrataLint.Scribe/StrataLint.Scribe.csproj", ScribeProject),
                ("tools/tests/Tests/Tests.csproj", TestsProject)),
            changedPaths,
            out var failure);
        var explicitInputPlan = EngineeringTestPlanPolicy.Evaluate(changedPaths, map, compiled, failure);

        Assert.Equal(EngineeringTestPlanKind.Full, fullPlan.Kind);
        Assert.Null(failure);
        var selected = Assert.Single(explicitInputPlan.Tests);
        Assert.Equal(EngineeringSelectedTestReason.CompiledInput, selected.Reason);
    }

    [Fact]
    public void TestProjectThatDirectlyCompilesTheContentGlobIsStillSelectedWholesale()
    {
        var changedPaths = new[] { "Blueprint/D5/X/Y.scribe.cs" };
        var compiled = EngineeringCompileInputDeriver.FindAffectedTestProjects(
            ProjectSnapshot(
                ("tools/StrataLint.Scribe/StrataLint.Scribe.csproj", ScribeProject),
                ("tools/tests/Tests/Tests.csproj", TestsProjectWithDirectContentGlob)),
            changedPaths,
            out var failure);
        var plan = EngineeringTestPlanPolicy.Evaluate(
            changedPaths,
            Map(Method("FirstClosedMethod"), Method("SecondClosedMethod")),
            compiled,
            failure);

        Assert.Null(failure);
        Assert.Equal(2, plan.Tests.Length);
        Assert.All(plan.Tests, static test => Assert.Equal(EngineeringSelectedTestReason.CompiledInput, test.Reason));
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
        Assert.DoesNotContain(plan.Tests, static test =>
            test.Reason == EngineeringSelectedTestReason.CompiledInput
            && test.ProjectPath.EndsWith("StrataLint.Scribe.Tests.csproj", StringComparison.Ordinal));
        var consumer = plan.Tests.First(static test =>
            test.Reason == EngineeringSelectedTestReason.UnknownInput
            && test.ProjectPath.EndsWith("StrataLint.Scribe.Tests.csproj", StringComparison.Ordinal));
        Assert.Equal(0, exitCode);
        var call = Assert.Single(calls);
        Assert.Equal("tools/StrataLint.sln", call.Target);
        Assert.Contains(consumer.Id, call.Filter, StringComparison.Ordinal);
    }

    private static ScribeTestMap EmptyMap() => Map();

    private static IReadOnlySet<string> EmptyProjects() => new HashSet<string>(StringComparer.Ordinal);

    private static ScribeTestMethod Method(
        string id,
        IReadOnlyList<string>? paths = null,
        bool unknown = false) => new(
        "tools/tests/Tests",
        $"tools/tests/Tests/{id}.cs",
        $"Tests.{id}",
        paths ?? [],
        unknown ? [TestMapUnknownReason.VariablePath] : []);

    private static RepositorySnapshot ProjectSnapshot(params (string Path, string Content)[] files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(static file =>
            RawRepositoryEntry.FromText(file.Path, file.Content)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

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

    private const string ScribeProject = """
        <Project Sdk="Microsoft.NET.Sdk">
          <ItemGroup>
            <Compile Include="../../Blueprint/**/*.scribe.cs" />
            <Compile Include="../../Shared/Generated.cs" />
          </ItemGroup>
        </Project>
        """;

    private const string TestsProject = """
        <Project Sdk="Microsoft.NET.Sdk">
          <ItemGroup>
            <ProjectReference Include="../../StrataLint.Scribe/StrataLint.Scribe.csproj" />
            <PackageReference Include="xunit" />
          </ItemGroup>
        </Project>
        """;

    private const string TestsProjectWithDirectContentGlob = """
        <Project Sdk="Microsoft.NET.Sdk">
          <ItemGroup>
            <Compile Include="../../../Blueprint/**/*.scribe.cs" />
            <ProjectReference Include="../../StrataLint.Scribe/StrataLint.Scribe.csproj" />
            <PackageReference Include="xunit" />
          </ItemGroup>
        </Project>
        """;
}
