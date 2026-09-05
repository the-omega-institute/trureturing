using StrataLint.Engine;
using StrataLint.EngineeringScope;

namespace StrataLint.ArchitectureTests;

public sealed partial class ScriptTestGateClosureTests
{
    /// <summary>
    /// 判官在依赖偏序下方、引用不到测试程序集,故只能以**名字**指代这几个脚手架类型。
    /// 名字与类型之间因此是一条没有编译器把关的引用 —— PR #5324 正是踩在这里:
    /// 脚手架迁移到另一个程序集后,判官侧的字符串未同步,编译不红,dev 合入后才红。
    ///
    /// 这条断言就是那条引用的机器判据:`typeof` 使类型名成为**编译期**绑定,
    /// 改名或删除该类型即 CS0246;改动判官侧常量则断言红。两侧任一漂移都在 PR 期暴露。
    /// </summary>
    [Fact]
    public void JudgeNamedHelperTypesResolveToDeclaredTypes()
    {
        Assert.Equal(
            ScriptTestInputDeriver.RepositoryLayoutAssemblyName,
            typeof(StrataLint.TestSupport.TestRepositoryLayout).Assembly.GetName().Name);
        Assert.Equal(
            ScriptTestInputDeriver.RepositoryLayoutTypeName,
            typeof(StrataLint.TestSupport.TestRepositoryLayout).Name);
        Assert.Equal(
            ScriptTestInputDeriver.RepositoryRelativePathTypeName,
            typeof(StrataLint.TestSupport.RepositoryRelativePath).Name);
        Assert.Equal(
            ScriptTestInputDeriver.ScriptHarnessScratchTypeName,
            typeof(StrataLint.TestSupport.ScriptHarnessScratch).Name);
        Assert.Equal(
            ScriptTestInputDeriver.ProcessRunnerTypeName,
            typeof(StrataLint.TestSupport.TestProcessRunner).Name);
    }

    private const string ScriptTestsProject =
        "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";
    private const string PlaybookScript =
        "tools/scripts/workflow/playbook-workflows.sh";
    private const string ScriptTestsSource =
        "tools/tests/StrataLint.ScriptTests/PlaybookWorkflowScriptTests.cs";
    private const string RepositoryRootCall = "TestRepositoryLayout." + "FindRoot()";
    private const string ProductionSnapshotRead = "GitRepositorySnapshotReader." + "ReadCurrent";
    private const string DirectoryFileEnumeration = "Directory." + "EnumerateFiles";
    private const string FileTextRead = "File." + "ReadAllText";

    [Fact]
    public void UnrelatedFullFallbackExcludesScriptTestsAndReportsSelected()
    {
        var snapshot = CurrentSnapshot();

        var plan = Evaluate(["CLAUDE.md"], snapshot, snapshot);

        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.DoesNotContain(ScriptTestsProject, plan.Projects);
        Assert.Contains("ScriptTests gate excluded", plan.Reason, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("Meta/Digestion/atoms/sha256/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
    [InlineData("Blueprint/D5/S3/GateProbe.scribe.cs")]
    [InlineData("D5/S3/GateProbe.lean")]
    public void ContentOnlyDeltaDoesNotSelectScriptTests(string changedPath)
    {
        var snapshot = CurrentSnapshot();

        var plan = Evaluate([changedPath], snapshot, snapshot);

        Assert.DoesNotContain(ScriptTestsProject, plan.Projects);
    }

    [Fact]
    public void RepositoryScriptInputRetainsScriptTestsOutOfFullFallback()
    {
        var snapshot = CurrentSnapshot();

        var plan = Evaluate([PlaybookScript], snapshot, snapshot);

        Assert.Contains(ScriptTestsProject, plan.Projects);
        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.Contains("ScriptTests gate included", plan.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void ReachedProjectDirectoryAndAncestorBuildInputSelectScriptTests()
    {
        var snapshot = CurrentSnapshot();

        var helperPlan = Evaluate(
            ["tools/tests/StrataLint.Tests/TestProcessRunner.cs"],
            snapshot,
            snapshot);
        var buildPlan = Evaluate(["Directory.Build.props"], snapshot, snapshot);

        Assert.Contains(ScriptTestsProject, helperPlan.Projects);
        Assert.Contains(ScriptTestsProject, buildPlan.Projects);
    }

    [Fact]
    public void ProtectedBaseTriggerStillSelectsAfterCandidateRemoval()
    {
        const string protectedScript = "tools/scripts/workflow/protected-gate-probe.sh";
        const string candidateScript = "tools/scripts/workflow/candidate-gate-probe.sh";
        var protectedBase = AppendTestMethod(
            CurrentSnapshot(),
            $$"""

                [Fact]
                public void ProtectedGateProbe()
                {
                    using var scratch = new TemporaryDirectory();
                    ScriptHarnessScratch.CopyScriptInto(
                        {{RootedPath(protectedScript)}},
                        Path.Combine(scratch.Path, "probe.sh"));
                }
            """,
            (protectedScript, "#!/usr/bin/env bash\nexit 0\n"));
        var candidate = WithoutFiles(WithFiles(
            ReplaceText(
                protectedBase,
                "tools/tests/StrataLint.ScriptTests/PlaybookWorkflowScriptTests.cs",
                text => text.Replace(protectedScript, candidateScript, StringComparison.Ordinal)),
            (candidateScript, "#!/usr/bin/env bash\nexit 0\n")),
            protectedScript);

        Assert.DoesNotContain(
            protectedScript,
            candidate.Files.Values.Single(file => file.Path.Value.EndsWith(
                "/PlaybookWorkflowScriptTests.cs",
                StringComparison.Ordinal)).Text,
            StringComparison.Ordinal);
        var candidateClosure = Derive(candidate, []);
        var plan = Evaluate([protectedScript], protectedBase, candidate);

        Assert.DoesNotContain(protectedScript, candidateClosure.ExactPaths);
        Assert.DoesNotContain(
            candidateClosure.DirectoryPrefixes,
            prefix => protectedScript.StartsWith(prefix + "/", StringComparison.Ordinal));
        Assert.Contains(ScriptTestsProject, plan.Projects);
    }

    [Fact]
    public void CandidateAddedRepositoryInputSelectsScriptTests()
    {
        const string addedScript = "tools/scripts/workflow/candidate-gate-probe.sh";
        var protectedBase = CurrentSnapshot();
        var candidate = AppendTestMethod(
            protectedBase,
            $$"""

                [Fact]
                public void CandidateGateProbe()
                {
                    using var scratch = new TemporaryDirectory();
                    ScriptHarnessScratch.CopyScriptInto(
                        {{RootedPath(addedScript)}},
                        Path.Combine(scratch.Path, "probe.sh"));
                }
            """,
            (addedScript, "#!/usr/bin/env bash\nexit 0\n"));

        var plan = Evaluate([addedScript], protectedBase, candidate);

        Assert.Contains(ScriptTestsProject, plan.Projects);
    }

    [Fact]
    public void OwnedRepositoryInputAddsScriptTestsToOrdinarySelectedPlan()
    {
        const string project = "tools/Independent/Independent.csproj";
        const string script = "tools/Independent/fixture.sh";
        var snapshot = AppendTestMethod(
            WithFiles(CurrentSnapshot(), (project, "<Project Sdk=\"Microsoft.NET.Sdk\" />\n")),
            $$"""

                [Fact]
                public void IndependentOwnerProbe()
                {
                    using var scratch = new TemporaryDirectory();
                    ScriptHarnessScratch.CopyScriptInto(
                        {{RootedPath(script)}},
                        Path.Combine(scratch.Path, "probe.sh"));
                }
            """,
            (script, "#!/usr/bin/env bash\nexit 0\n"));

        var plan = Evaluate([script], snapshot, snapshot);

        Assert.Equal(EngineeringTestPlanKind.Selected, plan.Kind);
        Assert.Equal([ScriptTestsProject], plan.Projects.ToArray());
    }

    [Fact]
    public void TestSupportRepositoryLayoutFindRootResolvesRepositoryPath()
    {
        const string script = "tools/scripts/workflow/test-support-root-probe.sh";
        var snapshot = ReplaceText(
            CurrentSnapshot(),
            "tools/tests/StrataLint.Tests/TestProcessRunner.cs",
            text => text.Replace(
                "namespace StrataLint.Tests;",
                "namespace StrataLint.TestSupport;",
                StringComparison.Ordinal));
        snapshot = ReplaceText(
            snapshot,
            ScriptTestsSource,
            text => text.Replace(
                "using StrataLint.Engine;",
                "using StrataLint.Engine; using StrataLint.TestSupport;",
                StringComparison.Ordinal));
        snapshot = AppendTestMethod(
            snapshot,
            $$"""

                [Fact]
                public void TestSupportRootProbe()
                {
                    _ = File.ReadAllText(Path.Combine(
                        TestRepositoryLayout.FindRoot(),
                        "{{script}}"));
                }
            """,
            (script, "#!/usr/bin/env bash\nexit 0\n"));

        var closure = Derive(snapshot, []);

        Assert.Contains(script, closure.ExactPaths);
    }

    [Fact]
    public void InstanceTestRepositoryLayoutFindRootFailsClosedByMethodSymbol()
    {
        const string script = "tools/scripts/workflow/instance-root-lookalike.sh";
        var snapshot = AppendTestMethod(
            CurrentSnapshot(),
            $$"""

                [Fact]
                public void InstanceRootLookalikeProbe()
                {
                    _ = File.ReadAllText(Path.Combine(
                        new StrataLint.Lookalike.TestRepositoryLayout().FindRoot(),
                        "{{script}}"));
                }
            """,
            ("tools/tests/StrataLint.ScriptTests/LookalikeRepositoryLayout.cs",
                "namespace StrataLint.Lookalike; public sealed class TestRepositoryLayout "
                + "{ public string FindRoot() => string.Empty; }\n"),
            (script, "#!/usr/bin/env bash\nexit 0\n"));

        var error = Assert.ThrowsAny<Exception>(() => Derive(snapshot, []));

        Assert.Contains("InstanceRootLookalikeProbe", Flatten(error), StringComparison.Ordinal);
        Assert.Contains(
            "unresolved repository-rooted path expression",
            Flatten(error),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ForeignAssemblyTestRepositoryLayoutFindRootFailsClosedByOwnerIdentity()
    {
        const string script = "tools/scripts/workflow/foreign-root-lookalike.sh";
        var snapshot = AppendTestMethod(
            CurrentSnapshot(),
            $$"""

                [Fact]
                public void ForeignRootLookalikeProbe()
                {
                    _ = File.ReadAllText(Path.Combine(
                        StrataLint.Lookalike.TestRepositoryLayout.FindRoot(),
                        "{{script}}"));
                }
            """,
            ("tools/tests/StrataLint.ScriptTests/LookalikeRepositoryLayout.cs",
                "namespace StrataLint.Lookalike; public static class TestRepositoryLayout "
                + "{ public static string FindRoot() => string.Empty; }\n"),
            (script, "#!/usr/bin/env bash\nexit 0\n"));

        var error = Assert.ThrowsAny<Exception>(() => Derive(snapshot, []));

        Assert.Contains("ForeignRootLookalikeProbe", Flatten(error), StringComparison.Ordinal);
        Assert.Contains(
            "unresolved repository-rooted path expression",
            Flatten(error),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ProcessStartInfoNonFirstConstructorArgumentSelectsScriptTests() =>
        AssertCommandOperandSelectsScriptTests(
            "ProcessStartInfoConstructorProbe",
            "tools/scripts/workflow/process-start-info-constructor-probe.sh",
            "_ = new System.Diagnostics.ProcessStartInfo(\"/bin/bash\", "
            + InterpolatedRootedPath("tools/scripts/workflow/process-start-info-constructor-probe.sh")
            + ");");

    [Fact]
    public void ProcessStartInfoObjectInitializerPropertySelectsScriptTests() =>
        AssertCommandOperandSelectsScriptTests(
            "ProcessStartInfoInitializerProbe",
            "tools/scripts/workflow/process-start-info-initializer-probe.sh",
            "_ = new System.Diagnostics.ProcessStartInfo { FileName = \"/bin/bash\", Arguments = "
            + InterpolatedRootedPath("tools/scripts/workflow/process-start-info-initializer-probe.sh")
            + " };");

    [Fact]
    public void ProcessStartInfoArgumentListAdditionSelectsScriptTests() =>
        AssertCommandOperandSelectsScriptTests(
            "ProcessStartInfoArgumentListProbe",
            "tools/scripts/workflow/process-start-info-argument-list-probe.sh",
            "var startInfo = new System.Diagnostics.ProcessStartInfo(\"/bin/bash\"); "
            + "startInfo.ArgumentList.Add("
            + InterpolatedRootedPath("tools/scripts/workflow/process-start-info-argument-list-probe.sh")
            + ");");

    [Fact]
    public void TestProcessRunnerInterpolatedOperandSelectsScriptTests() =>
        AssertCommandOperandSelectsScriptTests(
            "TestProcessRunnerOperandProbe",
            "tools/scripts/workflow/test-process-runner-operand-probe.sh",
            "_ = TestProcessRunner.Run(\"/bin/bash\", ["
            + InterpolatedRootedPath("tools/scripts/workflow/test-process-runner-operand-probe.sh")
            + "], TestScratchRoot.Current.Path, TestBudgets.ScriptProcessHangGuard, 1024);");

    [Fact]
    public void RepositoryRootedExtensionReceiverFailsClosedWithinAuditedOperationTree()
    {
        const string script = "tools/scripts/workflow/extension-receiver-probe.sh";
        var protectedBase = CurrentSnapshot();
        var candidate = AppendTestMethod(
            protectedBase,
            $$"""

                [Fact]
                public void ExtensionReceiverProbe()
                {
                    {{InterpolatedRootedPath(script)}}.ReadRepositoryText();
                }
            """,
            (script, "#!/usr/bin/env bash\nexit 0\n"));
        candidate = ReplaceText(
            candidate,
            "tools/tests/StrataLint.ScriptTests/PlaybookWorkflowScriptTests.cs",
            text => text + $$"""

                internal static class ScriptGateReceiverProbeExtensions
                {
                    internal static string ReadRepositoryText(this string path) =>
                        {{FileTextRead}}(path);
                }
                """);

        var error = Assert.ThrowsAny<Exception>(() =>
            Evaluate([script], protectedBase, candidate));

        Assert.Contains("ExtensionReceiverProbe", Flatten(error), StringComparison.Ordinal);
        Assert.Contains("operation value", Flatten(error), StringComparison.Ordinal);
        Assert.Contains("ReadRepositoryText", Flatten(error), StringComparison.Ordinal);
    }

    [Fact]
    public void RepositoryRootProcessWorkingDirectoryResolvesRelativeCommandOperandIntoClosure()
    {
        const string script = "tools/scripts/workflow/relative-runner-probe.sh";
        var protectedBase = CurrentSnapshot();
        var candidate = AppendTestMethod(
            protectedBase,
            $$"""

                [Fact]
                public void RelativeRunnerProbe()
                {
                    _ = TestProcessRunner.Run(
                        "/bin/bash",
                        ["{{script}}"],
                        {{RepositoryRootCall}},
                        TestBudgets.ScriptProcessHangGuard,
                        1024);
                }
            """,
            (script, "#!/usr/bin/env bash\nexit 0\n"));

        var closure = Derive(candidate, []);
        var plan = Evaluate([script], protectedBase, candidate);

        Assert.Contains(script, closure.ExactPaths);
        Assert.Contains(ScriptTestsProject, plan.Projects);
    }

    [Fact]
    public void RepositoryRootProcessWorkingDirectoryWithUnresolvedRelativeOperandFailsClosed()
    {
        var protectedBase = CurrentSnapshot();
        var candidate = AppendTestMethod(
            protectedBase,
            $$"""

                [Fact]
                public void UnresolvedRelativeRunnerProbe()
                {
                    _ = TestProcessRunner.Run(
                        "/bin/bash",
                        [Path.Combine("tools", Environment.GetEnvironmentVariable("SCRIPT_GATE_PROBE")!)],
                        {{RepositoryRootCall}},
                        TestBudgets.ScriptProcessHangGuard,
                        1024);
                }
            """);

        var error = Assert.ThrowsAny<Exception>(() =>
            Evaluate(["CLAUDE.md"], protectedBase, candidate));

        Assert.Contains("UnresolvedRelativeRunnerProbe", Flatten(error), StringComparison.Ordinal);
        Assert.Contains("InvocationExpressionSyntax", Flatten(error), StringComparison.Ordinal);
    }

    [Fact]
    public void FullOverrideReturnsBeforeBrokenGateDerivation()
    {
        var protectedBase = CurrentSnapshot();
        var candidate = AppendTestMethod(
            protectedBase,
            $$"""

                [Fact]
                public void MissingInputProbe()
                {
                    using var scratch = new TemporaryDirectory();
                    ScriptHarnessScratch.CopyScriptInto(
                        {{RootedPath("tools/scripts/missing.sh")}},
                        Path.Combine(scratch.Path, "probe.sh"));
                }
            """);

        var plan = Evaluate(["CLAUDE.md"], protectedBase, candidate, full: true);

        Assert.Equal(EngineeringTestPlanKind.Full, plan.Kind);
        Assert.Contains(ScriptTestsProject, plan.Projects);
    }

    [Fact]
    public void MissingConsumedPathFailsClosedWithTestIdentity()
    {
        var protectedBase = CurrentSnapshot();
        var candidate = AppendTestMethod(
            protectedBase,
            $$"""

                [Fact]
                public void MissingInputProbe()
                {
                    using var scratch = new TemporaryDirectory();
                    ScriptHarnessScratch.CopyScriptInto(
                        {{RootedPath("tools/scripts/missing.sh")}},
                        Path.Combine(scratch.Path, "probe.sh"));
                }
            """);

        var error = Assert.ThrowsAny<Exception>(() =>
            Evaluate(["CLAUDE.md"], protectedBase, candidate));

        Assert.Contains("PlaybookWorkflowScriptTests.MissingInputProbe", Flatten(error), StringComparison.Ordinal);
        Assert.Contains("absent", Flatten(error), StringComparison.Ordinal);
    }

    [Fact]
    public void VariableRepositoryPathAtAuditedCopySinkFailsClosed()
    {
        var protectedBase = CurrentSnapshot();
        var candidate = AppendTestMethod(
            protectedBase,
            $$"""

                [Fact]
                public void VariableInputProbe()
                {
                    using var scratch = new TemporaryDirectory();
                    var suffix = Environment.GetEnvironmentVariable("SCRIPT_GATE_PROBE")!;
                    ScriptHarnessScratch.CopyScriptInto(
                        Path.Combine({{RepositoryRootCall}}, suffix),
                        Path.Combine(scratch.Path, "probe.sh"));
                }
            """);

        var error = Assert.ThrowsAny<Exception>(() =>
            Evaluate(["CLAUDE.md"], protectedBase, candidate));

        Assert.Contains("VariableInputProbe", Flatten(error), StringComparison.Ordinal);
        Assert.Contains("unresolved", Flatten(error), StringComparison.Ordinal);
    }

    [Fact]
    public void AuditedRepositoryDirectoryEnumerationFailsClosed()
    {
        var protectedBase = CurrentSnapshot();
        var candidate = AppendTestMethod(
            protectedBase,
            $$"""

                [Fact]
                public void RepositoryEnumerationProbe()
                {
                    _ = {{DirectoryFileEnumeration}}({{RepositoryRootCall}}).ToArray();
                }
            """);

        var error = Assert.ThrowsAny<Exception>(() =>
            Evaluate(["CLAUDE.md"], protectedBase, candidate));

        Assert.Contains("RepositoryEnumerationProbe", Flatten(error), StringComparison.Ordinal);
        Assert.Contains("directory-enumeration", Flatten(error), StringComparison.Ordinal);
    }

    [Fact]
    public void UnrecognisedInvocationArgumentSinkFailsClosedBySymbolIdentity()
    {
        var protectedBase = CurrentSnapshot();
        var candidate = AppendTestMethod(
            protectedBase,
            $$"""

                [Fact]
                public void LookalikeSinkProbe()
                {
                    GateLookalike.CopyScriptInto(
                        {{RootedPath("tools/scripts/lookalike.sh")}},
                        "ignored");
                }

                private static class GateLookalike
                {
                    internal static void CopyScriptInto(string source, string target) { }
                }
            """);

        var error = Assert.ThrowsAny<Exception>(() =>
            Evaluate(["CLAUDE.md"], protectedBase, candidate));

        Assert.Contains("LookalikeSinkProbe", Flatten(error), StringComparison.Ordinal);
        Assert.Contains("unrecognised-sink", Flatten(error), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(
        "ObjectCreationOperandProbe",
        "unrecognised-sink operation value",
        "_ = new System.IO.FileInfo(Path.Combine(" + RepositoryRootCall
        + ", \"tools/scripts/missing-object-creation.sh\"));")]
    [InlineData(
        "ImplicitObjectCreationOperandProbe",
        "unrecognised-sink operation value",
        "System.IO.StreamReader reader = new(Path.Combine(" + RepositoryRootCall
        + ", \"tools/scripts/missing-implicit-creation.sh\")); reader.Dispose();")]
    [InlineData(
        "AssignmentOperandProbe",
        "unrecognised-sink operation value",
        "var startInfo = new System.Diagnostics.ProcessStartInfo(); startInfo.WorkingDirectory = Path.Combine("
        + RepositoryRootCall + ", \"tools/scripts/missing-assignment.sh\");")]
    [InlineData(
        "IndexerOperandProbe",
        "unrecognised-sink operation value",
        "var paths = new System.Collections.Generic.Dictionary<string, string>(); _ = paths[Path.Combine("
        + RepositoryRootCall + ", \"tools/scripts/missing-indexer.sh\")];")]
    public void AuditedRepositoryRootedProbeValuesFailClosedWithDiagnostic(
        string testName,
        string diagnostic,
        string body)
    {
        var protectedBase = CurrentSnapshot();
        var candidate = AppendTestMethod(
            protectedBase,
            $"\n    [Fact]\n    public void {testName}()\n    {{\n        {body}\n    }}");

        var error = Assert.ThrowsAny<Exception>(() =>
            Evaluate(["CLAUDE.md"], protectedBase, candidate));

        Assert.Contains(testName, Flatten(error), StringComparison.Ordinal);
        Assert.Contains(diagnostic, Flatten(error), StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionRepositoryLoaderFailsClosed()
    {
        var protectedBase = CurrentSnapshot();
        var candidate = AppendTestMethod(
            protectedBase,
            $$"""

                [Fact]
                public void ProductionLoaderProbe()
                {
                    _ = {{ProductionSnapshotRead}}({{RepositoryRootCall}});
                }
            """);

        var error = Assert.ThrowsAny<Exception>(() =>
            Evaluate(["CLAUDE.md"], protectedBase, candidate));

        Assert.Contains("ProductionLoaderProbe", Flatten(error), StringComparison.Ordinal);
        Assert.Contains("production-loader", Flatten(error), StringComparison.Ordinal);
    }

    [Fact]
    public void ControllerRuntimeInputMustBeTracked()
    {
        var snapshot = CurrentSnapshot();

        var error = Assert.ThrowsAny<Exception>(() =>
            Derive(snapshot, ["tools/scripts/controller-input-missing.sh"]));

        Assert.Contains("controller-input-missing.sh", Flatten(error), StringComparison.Ordinal);
        Assert.Contains("absent", Flatten(error), StringComparison.Ordinal);
    }

    [Fact]
    public void ControllerClosureRejectsAnUntrackedAuthoritativeRuntimePath()
    {
        const string missing = "tools/scripts/report/report-supervisor.sh";
        var snapshot = WithoutFiles(CurrentSnapshot(), missing);
        var error = Assert.ThrowsAny<Exception>(() => ControllerClosure.Derive(snapshot));

        Assert.Contains(missing, Flatten(error), StringComparison.Ordinal);
        Assert.Contains("absent", Flatten(error), StringComparison.Ordinal);
    }

    [Fact]
    public void ControllerClosureSyntheticSnapshotHasExpectedMembership()
    {
        var snapshot = CurrentSnapshot();
        var pure = ControllerClosure.Derive(snapshot);
        var evaluatorPaths = pure.EvaluatorPaths;
        var ownerPaths = pure.OwnerPaths;
        var runtimePaths = ControllerClosure.RuntimePaths;

        // B8 是**编译期类型保证,不是运行时钉子**,如实记账:这里的静态类型就是
        // ControllerClosurePaths,它不声明 Commit;只有 HEAD 适配器返回的
        // ControllerClosureSnapshot 才带真实 commit 身份。原先用
        // typeof(...).GetProperty("Commit") 做运行时断言,但反射使 ScribeTestMapDeriver
        // 无法解析本方法,SL-003 对每条新引入的 conservative unknown 逐条 Block。
        // 故撤下该断言;若 Commit 重新出现在 ControllerClosurePaths 上,**没有测试会红**,
        // 只能由评审发现 —— 不冒领它仍被机器守着。
        Assert.NotEmpty(runtimePaths);
        Assert.All(runtimePaths, path => Assert.Contains(path, evaluatorPaths));
        Assert.Contains("tools/StrataLint.EngineeringScope/Program.cs", evaluatorPaths);
        Assert.Contains("tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj", evaluatorPaths);
        Assert.Contains("tools/StrataLint.EngineeringScope/packages.lock.json", evaluatorPaths);
        Assert.Contains("Directory.Build.props", evaluatorPaths);
        Assert.Contains("tools/scripts/report/report-supervisor.sh", evaluatorPaths);
        Assert.Contains(".github/workflows/ci.yml", ownerPaths);
        Assert.DoesNotContain(".github/workflows/ci.yml", evaluatorPaths);
    }

    [Fact]
    public void ClosureDerivesReferencesPrefixesLocksBuildInputsAndControllerInputs()
    {
        const string controllerInput = "tools/scripts/controller-gate-probe.sh";
        const string syntheticProject = "tools/ScriptGateProbe/ScriptGateProbe.csproj";
        var snapshot = WithFiles(
            ReplaceText(
                CurrentSnapshot(),
                ScriptTestsProject,
                text => text.Replace(
                    "<ProjectReference Include=\"../../StrataLint.Engine/StrataLint.Engine.csproj\" />",
                    "<ProjectReference Include=\"../../StrataLint.Engine/StrataLint.Engine.csproj\" />\n"
                    + "    <ProjectReference Include=\"../../ScriptGateProbe/ScriptGateProbe.csproj\" />",
                    StringComparison.Ordinal)),
            (syntheticProject, "<Project Sdk=\"Microsoft.NET.Sdk\" />\n"),
            ("tools/ScriptGateProbe/Probe.cs", "namespace ScriptGateProbe; internal sealed class Probe { }\n"),
            ("tools/ScriptGateProbe/packages.lock.json", "{\"version\":1,\"dependencies\":{}}\n"),
            (controllerInput, "#!/usr/bin/env bash\nexit 0\n"));

        var closure = Derive(snapshot, [controllerInput]);

        Assert.Contains(ScriptTestsProject, closure.ExactPaths);
        Assert.Contains(syntheticProject, closure.ExactPaths);
        Assert.Contains("tools/ScriptGateProbe/packages.lock.json", closure.ExactPaths);
        Assert.Contains("tools/ScriptGateProbe", closure.DirectoryPrefixes);
        Assert.Contains("Directory.Build.props", closure.ExactPaths);
        Assert.Contains("global.json", closure.ExactPaths);
        Assert.Contains(controllerInput, closure.ExactPaths);
        Assert.DoesNotContain(
            closure.DirectoryPrefixes,
            static prefix => prefix.StartsWith("Blueprint", StringComparison.Ordinal));
        Assert.DoesNotContain(
            closure.ExactPaths,
            static path => path.EndsWith(".scribe.cs", StringComparison.Ordinal));
    }

    private static EngineeringTestPlan Evaluate(
        IReadOnlyList<string> changedPaths,
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        bool full = false)
    {
        return EngineeringTestPlanPolicy.Evaluate(
            changedPaths,
            protectedBase,
            candidate,
            [],
            [],
            full);
    }

    private static GateClosureView Derive(
        RepositorySnapshot snapshot,
        IReadOnlyCollection<string> controllerInputs)
    {
        var result = ScriptTestGateClosurePolicy.Derive(snapshot, controllerInputs);
        return new GateClosureView(result.ExactPaths, result.DirectoryPrefixes);
    }

    private static string RootedPath(string path) =>
        $"Path.Combine({RepositoryRootCall}, \"{path}\")";

    private static string InterpolatedRootedPath(string path) =>
        "$\"{" + RepositoryRootCall + "}/" + path + "\"";

    private static RepositorySnapshot AppendTestMethod(
        RepositorySnapshot snapshot,
        string method,
        params (string Path, string Content)[] addedFiles)
    {
        var updated = ReplaceText(
            snapshot,
            ScriptTestsSource,
            text => text[..text.LastIndexOf('}')] + method + "\n}\n");
        return WithFiles(updated, addedFiles);
    }

    private static void AssertCommandOperandSelectsScriptTests(
        string testName,
        string script,
        string body)
    {
        var snapshot = AppendTestMethod(
            CurrentSnapshot(),
            $"\n    [Fact]\n    public void {testName}()\n    {{\n        {body}\n    }}",
            (script, "#!/usr/bin/env bash\nexit 0\n"));

        var plan = Evaluate([script], snapshot, snapshot);

        Assert.Contains(ScriptTestsProject, plan.Projects);
    }

    private static RepositorySnapshot ReplaceText(
        RepositorySnapshot snapshot,
        string path,
        Func<string, string> replace)
    {
        var file = snapshot.Files.Values.Single(item => item.Path.Value == path);
        return WithFiles(snapshot, (path, replace(file.Text)));
    }

    private static RepositorySnapshot WithFiles(
        RepositorySnapshot snapshot,
        params (string Path, string Content)[] replacements)
    {
        var replacementByPath = replacements.ToDictionary(static item => item.Path, StringComparer.Ordinal);
        var entries = snapshot.Files.Values
            .Where(file => !replacementByPath.ContainsKey(file.Path.Value))
            .Select(file => new RawRepositoryEntry(file.Path.Value, file.RawBytes, file.GitBlobOid))
            .Concat(replacements.Select(static item => RawRepositoryEntry.FromText(item.Path, item.Content)));
        return Decode(RawRepositorySnapshot.Create(entries));
    }

    private static RepositorySnapshot WithoutFiles(
        RepositorySnapshot snapshot,
        params string[] removedPaths) =>
        Decode(RawRepositorySnapshot.Create(snapshot.Files.Values
            .Where(file => !removedPaths.Contains(file.Path.Value, StringComparer.Ordinal))
            .Select(file => new RawRepositoryEntry(file.Path.Value, file.RawBytes, file.GitBlobOid))));

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidDataException(failure.Message),
        };

    private static string Flatten(Exception exception) =>
        string.Join(" | ", ExceptionChain(exception).Select(static item => item.Message));

    private static IEnumerable<Exception> ExceptionChain(Exception exception)
    {
        for (var current = exception; current is not null; current = current.InnerException)
            yield return current;
    }

    private sealed record GateClosureView(
        IReadOnlyList<string> ExactPaths,
        IReadOnlyList<string> DirectoryPrefixes);
}
