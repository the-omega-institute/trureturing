using StrataLint.Engine;
using StrataLint.EngineeringScope;

namespace StrataLint.ArchitectureTests;

// ScriptTestGateClosureTests 的后半:operand / closure 判定一族。
// 分出来的直接理由是余量:宿主原 795 行,离 SL-003 的 800 行硬线只剩 5 行。
// 该类本就是 partial(同族已有 .Fixture.cs),故切分不动类声明。
//
// 切点用「缩进 4 的真方法收尾」判定,不是文本搜 `public void` ——
// 本文件大量 `public void XxxProbe()` 住在 const string source = """…""" 的**样本源码**里
// (缩进 16),按文本找边界会切进字符串字面量。

public sealed partial class ScriptTestGateClosureTests
{
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
