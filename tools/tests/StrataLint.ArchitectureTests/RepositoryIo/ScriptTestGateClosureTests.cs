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
}
