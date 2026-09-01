namespace StrataLint.ArchitectureTests;

public sealed class EngineeringPathFilterTests
{
    [Fact]
    public void ToolsChangePlansFullAndExecutesTheWholeSolution()
    {
        var plan = EngineeringTestPlanPolicy.Evaluate(
            ["tools/StrataLint.Engine/RepositoryIo/EngineeringTestPlanPolicy.cs"],
            EmptyMap());
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
    public void ScribeChangeExecutesDeclaredAndUnknownTargetsButNotUnrelatedTarget()
    {
        const string changedPath = "Blueprint/D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact.scribe.cs";
        var map = Map(
            new ScribeTestMethod(
                "tools/tests/StrataLint.Scribe.Tests",
                "tools/tests/StrataLint.Scribe.Tests/EmissionTests.cs",
                "EmissionTests.Related",
                [changedPath],
                []),
            new ScribeTestMethod(
                "tools/tests/StrataLint.Tests",
                "tools/tests/StrataLint.Tests/ProductionEnvironmentTests.cs",
                "ProductionEnvironmentTests.ReadsRepository",
                [],
                [TestMapUnknownReason.VariablePath]),
            new ScribeTestMethod(
                "tools/tests/StrataLint.Scribe.Tests",
                "tools/tests/StrataLint.Scribe.Tests/UnrelatedTests.cs",
                "UnrelatedTests.UsesSyntheticFixture",
                [],
                []));
        var plan = EngineeringTestPlanPolicy.Evaluate([changedPath], map);
        var calls = new List<EngineeringTestInvocation>();

        var exitCode = EngineeringTestExecutor.Execute(plan, invocation =>
        {
            calls.Add(invocation);
            return 0;
        });

        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Contains(plan.Tests, static test =>
            test is { Id: "EmissionTests.Related", Reason: EngineeringSelectedTestReason.DeclaredInput });
        Assert.Contains(plan.Tests, test => test.Id.Contains("ProductionEnvironmentTests", StringComparison.Ordinal));
        Assert.DoesNotContain(plan.Tests, test => test.Id.Contains("UnrelatedTests", StringComparison.Ordinal));
        Assert.Equal(0, exitCode);
        var call = Assert.Single(calls);
        Assert.Equal("tools/StrataLint.sln", call.Target);
        Assert.Contains("EmissionTests.Related", call.Filter, StringComparison.Ordinal);
        Assert.Contains("ProductionEnvironmentTests.ReadsRepository", call.Filter, StringComparison.Ordinal);
        Assert.DoesNotContain("UnrelatedTests", call.Filter, StringComparison.Ordinal);
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
            map);
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
            map);

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
            map);
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
            test.Reason == EngineeringSelectedTestReason.DeclaredInput
            && test.ProjectPath.EndsWith("StrataLint.Scribe.Tests.csproj", StringComparison.Ordinal));
        Assert.Equal(0, exitCode);
        var call = Assert.Single(calls);
        var consumer = plan.Tests.First(static test =>
            test.Reason == EngineeringSelectedTestReason.DeclaredInput
            && test.ProjectPath.EndsWith("StrataLint.Scribe.Tests.csproj", StringComparison.Ordinal));
        Assert.Equal("tools/StrataLint.sln", call.Target);
        Assert.Contains(consumer.Id, call.Filter, StringComparison.Ordinal);
    }

    /// <summary>
    /// `IsFullSurface` 的 reason 串自称 "a repository-root build input",而谓词判的是**任何**仓根文件。
    /// 仓根文档不是构建输入:构建图不读它,读其内容的测试为零(2026-08-30 实测),
    /// 而「本次改动把某文件顶过 800 行」由 admission 的 SL-003 delta 分支无条件 Block,
    /// 与 engineering 计划无关。故文档改动走正常 selected 选择,不再连坐全量。
    /// </summary>
    [Fact]
    public void RepositoryRootDocumentChangeIsSelectedRatherThanForcingTheWholeSolution()
    {
        var map = Map(new ScribeTestMethod(
            "tools/tests/StrataLint.Tests",
            "tools/tests/StrataLint.Tests/ProductionEnvironmentTests.cs",
            "ProductionEnvironmentTests.ReadsRepository",
            [],
            [TestMapUnknownReason.VariablePath]));

        foreach (var document in new[] { "CLAUDE.md", "AGENTS.md", "README.md" })
        {
            var plan = EngineeringTestPlanPolicy.Evaluate(
                [document],
                map);

            Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        }
    }

    /// <summary>
    /// 放行侧不能单独立;窄化必须同时钉住**仍然**转 Full 的那一侧,否则一个「什么都放行」的
    /// 谓词也能通过上一条。仓根的构建输入逐个点名,且一个不在文档名单里的新增仓根文件
    /// 必须仍然转 Full —— 谓词是白名单式排除,新增项 fail-closed。
    /// </summary>
    [Theory]
    [InlineData("Directory.Build.props")]
    [InlineData("Directory.Packages.props")]
    [InlineData("Makefile")]
    [InlineData("global.json")]
    [InlineData("lean-toolchain")]
    [InlineData("lakefile.toml")]
    [InlineData("lake-manifest.json")]
    [InlineData("Trureturing.lean")]
    [InlineData(".editorconfig")]
    [InlineData(".gitignore")]
    [InlineData("SomeUnclassifiedNewRootFile.txt")]
    public void RepositoryRootBuildInputStillForcesTheWholeSolution(string path)
    {
        var plan = EngineeringTestPlanPolicy.Evaluate(
            [path],
            EmptyMap());

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
    }

    private static ScribeTestMap EmptyMap() => Map();

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
