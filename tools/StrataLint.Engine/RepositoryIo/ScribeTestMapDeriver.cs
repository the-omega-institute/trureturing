using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal enum TestMapUnknownReason
{
    VariablePath,
    DirectoryEnumeration,
    IndirectViaProductionLoader,
    RepositoryRootMarker,
    Other,
}

internal sealed record TestMapSource(
    string Path,
    string Content,
    string PartitionKey = "synthetic");

internal sealed record ScribeTestMethod(
    string PartitionKey,
    string SourcePath,
    string Id,
    IReadOnlyList<string> Paths,
    IReadOnlyList<TestMapUnknownReason> UnknownReasons,
    bool IsStaticallySkipped = false)
{
    internal bool IsUnknown => UnknownReasons.Count != 0;

    internal string Identity => $"{SourcePath}::{Id}";

    internal string DisplayIdentity => $"{PartitionKey}::{Id}";
}

internal sealed record ScribeTestMap(
    IReadOnlyList<ScribeTestMethod> Methods,
    IReadOnlyList<string> UnclassifiedManagedProjectPaths,
    IReadOnlyList<string> OrphanManagedSourcePaths,
    IReadOnlyList<string> DanglingCompileFailProofProjectExemptionPaths,
    IReadOnlyDictionary<string, string> CompileProjectBySourcePath,
    IReadOnlyList<MsBuildCompileFinding> CompileQueryFindings);

internal sealed record ScribeTestProjectPartition(string Key, string ProjectPath);

internal sealed record ScribeTrackedSource(string Path, string Content);

internal static class ScribeTestMapDeriver
{
    private const string ManagedTestProjectPrefix = "tools/tests/";

    // These projects are deliberately compiled to fail by preflight. Keep this declaration
    // removal-only: a new non-xUnit project must first establish its own governed class rather
    // than silently extending the exception set.
    internal static readonly IReadOnlySet<string> CompileFailProofProjectExemptions =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj",
            "tools/tests/CompileFailProof/CompileFailProof.csproj",
        };

    // This list governs the declared-path debt check. Entries are either exact files or directory
    // roots; engineering scope is derived from consumers and does not use this declaration.
    internal static readonly IReadOnlyList<string> DeclaredPathWhitelist =
    [
        // CLI linkage governance derives callers from the tracked harness scripts.
        ".github/scripts",
        // 消化退出 CI 后,ci.yml 是仓内唯一的 workflow;守卫「无 workflow 代跑消化」
        // 与 lake 缓存契约都声明式读它(此前二者读的是已删除的 theory-ingest.yml)。
        ".github/workflows/ci.yml",
        "Blueprint",
        "CLAUDE.md",
        "D5",
        "D5/X_Frontier/ValuesProducer.lean",
        "Generated",
        "Golden",
        "Golden/Projection",
        "Golden/values-kernels.toml",
        "Library",
        "Meta",
        "Meta/Digestion/backfill",
        "Meta/FILEMAP.toml",
        "global.json",
        "lakefile.toml",
        "lean-toolchain",
        // Skill packages are read by architecture tests that pin each skill's structural
        // contract; the directory is declared rather than each file so that adding a skill
        // test does not require editing this deriver.
        "skills",
        "tools",
        "tools/tests/StrataLint.ArchitectureTests",
        "tools/tests/StrataLint.Scribe.Tests",
        "tools/tests/StrataLint.Tests",
        "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml",
        // 派发契约测试按 Makefile 的字面内容判断目标与前置，故它是一个声明的读取路径。
        "Makefile",
    ];

    internal static bool IsDeclaredPathAllowed(string path) =>
        DeclaredPathWhitelist.Any(allowed => path == allowed
            || path.StartsWith(allowed + "/", StringComparison.Ordinal));

    internal static ScribeTestMap DeriveRepository(
        string repositoryRoot,
        string? dotnetExecutable = null,
        TimeSpan? timeout = null)
    {
        var files = GitIndexRepositoryFiles.Enumerate(repositoryRoot);
        var tracked = files
            .Where(static file => file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
                || file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(file => new ScribeTrackedSource(
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .ToArray();
        var projectPaths = tracked
            .Where(static file => file.Path.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(static file => file.Path);
        return DeriveTracked(
            tracked,
            MsBuildCompileOracle.Query(repositoryRoot, projectPaths, dotnetExecutable, timeout));
    }

    internal static ScribeTestMap DeriveSnapshot(RepositorySnapshot snapshot)
    {
        var tracked = snapshot.Files.Values
            .Where(static file => file.Path.Value.EndsWith(".cs", StringComparison.Ordinal)
                || file.Path.Value.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(static file => new ScribeTrackedSource(file.Path.Value, file.Text))
            .ToArray();
        var projects = tracked
            .Where(static file => file.Path.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(static file => file.Path)
            .ToArray();
        if (projects.Length == 0)
        {
            return DeriveTracked(tracked, new MsBuildCompileMap(
                new Dictionary<string, string>(StringComparer.Ordinal),
                []));
        }

        try
        {
            using var checkout = MsBuildCompileOracle.Materialize(snapshot);
            return DeriveTracked(tracked, MsBuildCompileOracle.Query(checkout.Root, projects));
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
        {
            return DeriveTracked(tracked, new MsBuildCompileMap(
                new Dictionary<string, string>(StringComparer.Ordinal),
                projects.Select(project => new MsBuildCompileFinding(
                    project,
                    $"MSBuild snapshot materialization failed closed: {exception.Message}"))
                    .ToArray()));
        }
    }

    internal static IReadOnlyList<ScribeTestProjectPartition> DeriveProjectPartitions(
        IEnumerable<(string Path, string Content)> projectFiles) => projectFiles
        .Where(static project => IsXunitProject(project.Content))
        .Select(static project => new ScribeTestProjectPartition(
            ProjectDirectory(project.Path),
            project.Path))
        .OrderBy(static partition => partition.Key, StringComparer.Ordinal)
        .ToArray();

    internal static IReadOnlyList<string> FindUnclassifiedManagedProjects(
        IEnumerable<(string Path, string Content)> projectFiles) => projectFiles
        .Where(static project => project.Path.StartsWith(ManagedTestProjectPrefix, StringComparison.Ordinal))
        .Where(project => !IsXunitProject(project.Content)
            && !CompileFailProofProjectExemptions.Contains(project.Path))
        .Select(static project => project.Path)
        .Order(StringComparer.Ordinal)
        .ToArray();

    // #3670:hang-guard 预算的声明写着「never bears a test verdict」,但那只是**声明** ——
    // 只有走 `TestProcessRunner` 时超时才变成 `SkipException`;走 `BoundedProcessRunner`
    // 时它抛 `TimeoutException`,于是**恰好承担了判词**。本判据把声明与路由钉在一起。
    //
    // **归因的诚实交代(一轮评审在同族改动上判过这一点)**:本方法自己读 `tools/tests/**`,
    // 而 `ScribeTestMapDeriver` 的 declared/unknown 账**看不见**这次读取 ——
    // 调用方的方法体里只有一个它不识别的名字。当前它仍可达,**理由是
    // `EngineeringTestPlanPolicy.IsFullSurface` 把 `tools/` 下任何改动转 Full**,
    // 不是因为归因成立。**不得把「住在 Engine、受 SL-022 保护」冒充为「I/O 已归因」。**
    // 正确收口是让这类 repository query 成为映射器可归因的 governed read;那是一条独立的工作。
    //
    // **判据的已知反例集合(不完整,逐条写出来)**:本方法按 XML 结构判 `PackageReference` /
    // `AdditionalFiles` / `NoWarn`,故比子串强;但它**看不见**:
    // ① 观察者本身被删除或从 `Compile` 排除(#3416 的 test-identity gap);
    // ② `IncludeAssets`/`ExcludeAssets` 排除 analyzers;
    // ③ `Directory.Build.props` 等继承来的 `NoWarn` / `WarningsNotAsErrors` / ruleset / globalconfig;
    // ④ 经 MSBuild 属性或 import 间接给出的 `Include` 值;
    // ⑤ 源文件内的 `#pragma warning disable RS0030` 与 `.editorconfig` 严重性降级。
    internal static IReadOnlyList<string> FindUnroutedHangGuardCalls(string repositoryRoot)
    {
        var offenders = new List<string>();
        foreach (var file in GitIndexRepositoryFiles.Enumerate(repositoryRoot))
        {
            if (!file.RelativePath.StartsWith(ManagedTestProjectPrefix, StringComparison.Ordinal)
                || !file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
                || file.RelativePath.EndsWith("/TestProcessRunner.cs", StringComparison.Ordinal))
            {
                continue;
            }

            var source = File.ReadAllText(file.FullPath);
            offenders.AddRange(UnroutedHangGuardCalls(file.RelativePath, source));
        }

        return offenders.Order(StringComparer.Ordinal).ToArray();
    }

    private static IEnumerable<string> UnroutedHangGuardCalls(string path, string source)
    {
        const string Call = "BoundedProcessRunner.Run(";
        for (var index = source.IndexOf(Call, StringComparison.Ordinal);
             index >= 0;
             index = source.IndexOf(Call, index + Call.Length, StringComparison.Ordinal))
        {
            // raw-string literal 里的示例代码不是真调用。
            if (CountText(source[..index], "\"\"\"") % 2 == 1)
            {
                continue;
            }

            // 取**该调用自己的实参列表**(括号平衡)。固定窗口会跨进相邻调用:
            // 第一版正因此把一处**故意**用 `ZeroDuration` 的调用误报为违规。
            var arguments = BalancedArguments(source, index + Call.Length);
            if (arguments.Contains("HangGuard", StringComparison.Ordinal)
                || arguments.Contains("HangDetectionBudget", StringComparison.Ordinal))
            {
                yield return $"{path}:{CountText(source[..index], "\n") + 1}";
            }
        }
    }

    private static string BalancedArguments(string source, int start)
    {
        var depth = 0;
        for (var index = start; index < source.Length; index++)
        {
            if (source[index] == '(')
            {
                depth++;
            }
            else if (source[index] == ')')
            {
                if (depth == 0)
                {
                    return source[start..index];
                }

                depth--;
            }
        }

        return source[start..];
    }

    private static int CountText(string text, string needle)
    {
        var count = 0;
        var index = text.IndexOf(needle, StringComparison.Ordinal);
        while (index >= 0)
        {
            count++;
            index = text.IndexOf(needle, index + needle.Length, StringComparison.Ordinal);
        }

        return count;
    }

    internal static IReadOnlyList<string> FindOrphanManagedSources(
        IEnumerable<string> sourcePaths,
        IReadOnlyDictionary<string, string> projectBySourcePath) => sourcePaths
        .Where(path => !projectBySourcePath.ContainsKey(path))
        .Order(StringComparer.Ordinal)
        .ToArray();

    internal static IReadOnlyList<string> FindDanglingCompileFailProofProjectExemptions(
        IEnumerable<string> projectPaths)
    {
        var projects = projectPaths.ToHashSet(StringComparer.Ordinal);
        return CompileFailProofProjectExemptions
            .Where(path => !projects.Contains(path))
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    private static string ProjectDirectory(string projectPath) =>
        projectPath.LastIndexOf('/') is var slash && slash >= 0 ? projectPath[..slash] : ".";

    private static ScribeTestMap DeriveTracked(
        IReadOnlyList<ScribeTrackedSource> tracked,
        MsBuildCompileMap compileMap)
    {
        var projectFiles = tracked
            .Where(static file => file.Path.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(static file => (file.Path, file.Content))
            .ToArray();
        var sources = tracked
            .Where(static file => file.Path.EndsWith(".cs", StringComparison.Ordinal))
            .ToArray();
        var testProjects = DeriveProjectPartitions(projectFiles)
            .ToDictionary(static project => project.ProjectPath, StringComparer.Ordinal);
        var testSources = sources
            .Where(source => compileMap.ProjectBySourcePath.TryGetValue(source.Path, out var project)
                && testProjects.ContainsKey(project))
            .Select(source => new TestMapSource(
                source.Path,
                source.Content,
                testProjects[compileMap.ProjectBySourcePath[source.Path]].Key))
            .ToArray();
        var productionSources = sources
            .Where(source => compileMap.ProjectBySourcePath.TryGetValue(source.Path, out var project)
                && !testProjects.ContainsKey(project))
            .Select(source => new RepositoryReadSource(
                Path.GetFileNameWithoutExtension(compileMap.ProjectBySourcePath[source.Path]),
                source.Path,
                source.Content))
            .ToArray();
        var indirectSites = ProductionRepositoryReadDeriver.InspectTests(productionSources, testSources)
            .Select(static site => (site.Path, site.Line));
        return DeriveSources(
            testSources,
            indirectSites,
            FindUnclassifiedManagedProjects(projectFiles),
            compileMap.Findings.Count == 0
                ? FindOrphanManagedSources(
                    sources.Select(static source => source.Path),
                    compileMap.ProjectBySourcePath)
                : [],
            FindDanglingCompileFailProofProjectExemptions(
                projectFiles.Select(static project => project.Path)),
            compileMap.ProjectBySourcePath,
            compileMap.Findings);
    }

    internal static ScribeTestMap DeriveSources(
        IEnumerable<TestMapSource> sourceFiles,
        IEnumerable<(string Path, int Line)> indirectProductionSites,
        IReadOnlyList<string>? unclassifiedManagedProjectPaths = null,
        IReadOnlyList<string>? orphanManagedSourcePaths = null,
        IReadOnlyList<string>? danglingCompileFailProofProjectExemptionPaths = null,
        IReadOnlyDictionary<string, string>? compileProjectBySourcePath = null,
        IReadOnlyList<MsBuildCompileFinding>? compileQueryFindings = null)
    {
        var parsed = sourceFiles.Select(Parse).ToArray();
        var discoveryPaths = ExtractDiscoveryPaths(parsed);
        var methods = parsed.SelectMany(static source => source.Methods).ToArray();
        var methodsByTypeAndName = methods
            .GroupBy(static method => (method.TypeName, method.Name))
            .ToDictionary(static group => group.Key, static group => group.ToArray());
        var indirect = indirectProductionSites.ToArray();
        var results = new List<ScribeTestMethod>();

        foreach (var test in methods.Where(static method => method.IsTest))
        {
            var paths = new HashSet<string>(StringComparer.Ordinal);
            var reasons = new HashSet<TestMapUnknownReason>();
            var pending = new Stack<ParsedMethod>();
            var visited = new HashSet<ParsedMethod>();
            pending.Push(test);
            while (pending.TryPop(out var method))
            {
                if (!visited.Add(method))
                {
                    continue;
                }

                InspectMethod(method, discoveryPaths, paths, reasons);
                if (indirect.Any(site => site.Path == method.Path
                    && site.Line >= method.StartLine && site.Line <= method.EndLine))
                {
                    reasons.Add(TestMapUnknownReason.IndirectViaProductionLoader);
                }

                foreach (var call in LocalCalls(method.Syntax))
                {
                    if (methodsByTypeAndName.TryGetValue((method.TypeName, call), out var targets)
                        && targets.Length == 1)
                    {
                        pending.Push(targets[0]);
                    }
                    else if (targets is { Length: > 1 })
                    {
                        reasons.Add(TestMapUnknownReason.Other);
                    }
                }
            }

            results.Add(new ScribeTestMethod(
                test.PartitionKey,
                test.Path,
                $"{test.TypeName}.{test.Name}",
                paths.Order(StringComparer.Ordinal).ToArray(),
                reasons.Order().ToArray(),
                test.IsStaticallySkipped));
        }

        return new ScribeTestMap(
            results
                .OrderBy(static method => method.PartitionKey, StringComparer.Ordinal)
                .ThenBy(static method => method.SourcePath, StringComparer.Ordinal)
                .ThenBy(static method => method.Id, StringComparer.Ordinal)
                .ToArray(),
            unclassifiedManagedProjectPaths ?? [],
            orphanManagedSourcePaths ?? [],
            danglingCompileFailProofProjectExemptionPaths ?? [],
            compileProjectBySourcePath ?? new Dictionary<string, string>(StringComparer.Ordinal),
            compileQueryFindings ?? []);
    }

    private static bool IsXunitProject(string content)
    {
        var document = XDocument.Parse(content, LoadOptions.None);
        return document.Descendants().Any(static element =>
            element.Name.LocalName == "PackageReference"
            && string.Equals(
                (string?)element.Attribute("Include"),
                "xunit",
                StringComparison.OrdinalIgnoreCase));
    }

    private static void InspectMethod(
        ParsedMethod method,
        IReadOnlyDictionary<string, IReadOnlyList<string>?> discoveryPaths,
        HashSet<string> paths,
        HashSet<TestMapUnknownReason> reasons)
    {
        foreach (var invocation in method.Syntax.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            if (IsAccessorCall(invocation, "Discover"))
            {
                AddDiscoveryPaths(invocation, discoveryPaths, paths, reasons);
            }

            // 声明式仓库枚举(#2535 / PR #3799 第二轮评审):
            // `EnumerateDeclared(root, "<字面量前缀>")` 读 git index 而非目录,
            // 故**不记** `DirectoryEnumeration`;但它必须把那个前缀登记为 declared path,
            // 否则 `EngineeringTestPlanDeriver` 在只改该前缀下文件的 PR 上**不会选中该测试** ——
            // 一个观察者对它要观察的那类变更盲,等于没有。
            // 该缺口正是一次评审用「临时克隆只加一条 D5 .lean → planner 输出
            // cold_build_observer=[]」实测出来的。
            if (IsAccessorCall(invocation, "EnumerateDeclared"))
            {
                AddDeclaredPrefix(invocation, paths, reasons);
                continue;
            }

            if (IsAccessorCall(invocation, "EnumerateFiles"))
            {
                reasons.Add(TestMapUnknownReason.DirectoryEnumeration);
                AddLiteralCreatePath(invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression, paths, reasons);
                continue;
            }

            if (!IsAccessorCall(invocation, "ReadAllText", "ReadAllBytes", "FileExists", "CopyTo"))
            {
                continue;
            }

            if (IsAccessorCall(invocation, "ReadAllText", "ReadAllBytes")
                && IsDeclaredEnumerationFullPath(
                    invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression))
            {
                continue;
            }

            AddLiteralCreatePath(invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression, paths, reasons);
        }
    }

    // 只接受**字面量**前缀:变量前缀无法静态归因,按 fail-closed 记 VariablePath。
    private static void AddDeclaredPrefix(
        InvocationExpressionSyntax invocation,
        HashSet<string> paths,
        HashSet<TestMapUnknownReason> reasons)
    {
        if (TryGetDeclaredPrefix(invocation, out var prefix))
        {
            paths.Add(prefix);
            return;
        }

        reasons.Add(TestMapUnknownReason.VariablePath);
    }

    private static bool TryGetDeclaredPrefix(
        InvocationExpressionSyntax invocation,
        out string prefix)
    {
        var arguments = invocation.ArgumentList.Arguments;
        if (arguments.Count >= 2
            && arguments[1].Expression is LiteralExpressionSyntax literal
            && literal.IsKind(SyntaxKind.StringLiteralExpression))
        {
            prefix = literal.Token.ValueText.Replace('\\', '/');
            return true;
        }

        prefix = string.Empty;
        return false;
    }

    private static bool IsDeclaredEnumerationFullPath(ExpressionSyntax? argument)
    {
        if (argument is not MemberAccessExpressionSyntax
            {
                Expression: IdentifierNameSyntax entry,
                Name.Identifier.ValueText: "FullPath",
            })
        {
            return false;
        }

        var selector = argument.Ancestors().OfType<SimpleLambdaExpressionSyntax>()
            .FirstOrDefault(lambda =>
                lambda.Parameter.Identifier.ValueText == entry.Identifier.ValueText);
        if (selector?.Parent is not ArgumentSyntax
            {
                Parent: ArgumentListSyntax
                {
                    Parent: InvocationExpressionSyntax select,
                },
            })
        {
            return false;
        }

        if (select.Expression is not MemberAccessExpressionSyntax
            {
                Name.Identifier.ValueText: "Select",
                Expression: var source,
            })
        {
            return false;
        }

        while (source is InvocationExpressionSyntax invocation)
        {
            if (IsAccessorCall(invocation, "EnumerateDeclared"))
            {
                return TryGetDeclaredPrefix(invocation, out _);
            }

            if (invocation.Expression is not MemberAccessExpressionSyntax member)
            {
                return false;
            }

            source = member.Expression;
        }

        return false;
    }

    private static void AddLiteralCreatePath(
        ExpressionSyntax? argument,
        HashSet<string> paths,
        HashSet<TestMapUnknownReason> reasons)
    {
        var create = argument
            ?
            .DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
            .FirstOrDefault(static candidate => candidate.Expression is MemberAccessExpressionSyntax
            {
                Expression: IdentifierNameSyntax { Identifier.ValueText: "RepositoryRelativePath" },
                Name.Identifier.ValueText: "Create",
            });
        var expression = create?.ArgumentList.Arguments.SingleOrDefault()?.Expression;
        if (expression is LiteralExpressionSyntax literal
            && literal.IsKind(SyntaxKind.StringLiteralExpression))
        {
            paths.Add(literal.Token.ValueText.Replace('\\', '/'));
            return;
        }

        if (argument is InvocationExpressionSyntax
            {
                Expression: MemberAccessExpressionSyntax
                {
                    Expression: IdentifierNameSyntax { Identifier.ValueText: "Path" },
                    Name.Identifier.ValueText: "Combine",
                },
            } combine
            && combine.ArgumentList.Arguments is { Count: >= 2 } arguments
            && arguments[0].Expression is InvocationExpressionSyntax
            {
                Expression: MemberAccessExpressionSyntax
                {
                    Name.Identifier.ValueText: "FindRoot",
                } findRoot,
            }
            && findRoot.Expression.ToString().EndsWith("RepositoryLayout", StringComparison.Ordinal)
            && arguments.Skip(1).All(static item => item.Expression is LiteralExpressionSyntax
                { RawKind: (int)SyntaxKind.StringLiteralExpression }))
        {
            paths.Add(string.Join(
                '/',
                arguments.Skip(1).Select(static item => ((LiteralExpressionSyntax)item.Expression).Token.ValueText)));
            return;
        }

        reasons.Add(TestMapUnknownReason.VariablePath);
    }

    private static void AddDiscoveryPaths(
        InvocationExpressionSyntax invocation,
        IReadOnlyDictionary<string, IReadOnlyList<string>?> discoveryPaths,
        HashSet<string> paths,
        HashSet<TestMapUnknownReason> reasons)
    {
        var criterion = (invocation.ArgumentList.Arguments.LastOrDefault()?.Expression
            as MemberAccessExpressionSyntax)?.Name.Identifier.ValueText;
        if (criterion is not null
            && discoveryPaths.TryGetValue(criterion, out var markerPaths)
            && markerPaths is not null)
        {
            paths.UnionWith(markerPaths);
            return;
        }

        reasons.Add(TestMapUnknownReason.RepositoryRootMarker);
    }

    private static IReadOnlyDictionary<string, IReadOnlyList<string>?> ExtractDiscoveryPaths(
        IEnumerable<ParsedSource> sources)
    {
        var result = new Dictionary<string, IReadOnlyList<string>?>(StringComparer.Ordinal);
        var matches = sources.SelectMany(static source => source.Root.DescendantNodes()
            .OfType<MethodDeclarationSyntax>())
            .Where(static method => method.Identifier.ValueText == "Matches");
        foreach (var arm in matches.SelectMany(static method => method.DescendantNodes()
                     .OfType<SwitchExpressionArmSyntax>()))
        {
            var criteria = arm.Pattern.DescendantNodesAndSelf()
                .OfType<MemberAccessExpressionSyntax>()
                .Where(static member => member.Expression is IdentifierNameSyntax
                {
                    Identifier.ValueText: "RepositoryRootCriterion",
                })
                .Select(static member => member.Name.Identifier.ValueText)
                .Distinct(StringComparer.Ordinal)
                .ToArray();
            if (criteria.Length == 0)
            {
                continue;
            }

            var markerPaths = TryExtractMarkerPaths(arm.Expression);
            foreach (var criterion in criteria)
            {
                result[criterion] = markerPaths;
            }
        }

        return result;
    }

    private static IReadOnlyList<string>? TryExtractMarkerPaths(ExpressionSyntax expression)
    {
        var combines = expression.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>()
            .Where(static invocation => invocation.Expression is MemberAccessExpressionSyntax
            {
                Expression: IdentifierNameSyntax { Identifier.ValueText: "Path" },
                Name.Identifier.ValueText: "Combine",
            })
            .ToArray();
        var paths = new List<string>();
        foreach (var combine in combines)
        {
            var arguments = combine.ArgumentList.Arguments;
            if (arguments.Count < 2
                || arguments[0].Expression is not IdentifierNameSyntax { Identifier.ValueText: "root" })
            {
                return null;
            }

            var segments = new List<string>();
            foreach (var argument in arguments.Skip(1))
            {
                if (argument.Expression is not LiteralExpressionSyntax literal
                    || !literal.IsKind(SyntaxKind.StringLiteralExpression))
                {
                    return null;
                }

                segments.Add(literal.Token.ValueText);
            }

            paths.Add(string.Join('/', segments));
        }

        return paths.Count == 0 ? null : paths.Distinct(StringComparer.Ordinal).ToArray();
    }

    private static bool IsAccessorCall(InvocationExpressionSyntax invocation, params string[] names) =>
        invocation.Expression is MemberAccessExpressionSyntax member
        && names.Contains(member.Name.Identifier.ValueText, StringComparer.Ordinal)
        && !IsTemporaryFileSystemRoot(member.Expression)
        && (member.Expression.ToString().Contains("RepositoryAccessor", StringComparison.Ordinal)
            || member.Expression is IdentifierNameSyntax
            || member.Expression is MemberAccessExpressionSyntax
            || member.Expression is InvocationExpressionSyntax);

    private static bool IsTemporaryFileSystemRoot(ExpressionSyntax receiver)
    {
        while (receiver is MemberAccessExpressionSyntax member)
        {
            receiver = member.Expression;
        }

        return receiver is IdentifierNameSyntax { Identifier.ValueText: "TemporaryFileSystem" };
    }

    private static IEnumerable<string> LocalCalls(MethodDeclarationSyntax method) =>
        method.DescendantNodes().OfType<InvocationExpressionSyntax>()
            .Select(static invocation => invocation.Expression switch
            {
                IdentifierNameSyntax identifier => identifier.Identifier.ValueText,
                MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax, Name: var name } => name.Identifier.ValueText,
                _ => string.Empty,
            })
            .Where(static name => name.Length != 0);

    private static ParsedSource Parse(TestMapSource source)
    {
        var root = CSharpSyntaxTree.ParseText(source.Content).GetRoot();
        var methods = root.DescendantNodes().OfType<MethodDeclarationSyntax>().Select(method =>
        {
            var type = method.Ancestors().OfType<TypeDeclarationSyntax>().First();
            var span = method.GetLocation().GetLineSpan();
            return new ParsedMethod(
                source.Path,
                source.PartitionKey,
                type.Identifier.ValueText,
                method.Identifier.ValueText,
                method.AttributeLists.SelectMany(static list => list.Attributes).Any(IsTestAttribute),
                method.AttributeLists.SelectMany(static list => list.Attributes).Any(IsStaticallySkippedTestAttribute),
                span.StartLinePosition.Line + 1,
                span.EndLinePosition.Line + 1,
                method);
        }).ToArray();
        return new ParsedSource(root, methods);
    }

    private static bool IsTestAttribute(AttributeSyntax attribute) =>
        attribute.Name.ToString() is "Fact" or "FactAttribute" or "Theory" or "TheoryAttribute";

    private static bool IsStaticallySkippedTestAttribute(AttributeSyntax attribute) =>
        IsTestAttribute(attribute)
        && attribute.ArgumentList?.Arguments.Any(static argument =>
            argument.NameEquals?.Name.Identifier.ValueText == "Skip"
            && !argument.Expression.IsKind(SyntaxKind.NullLiteralExpression)) == true;

    private sealed record ParsedSource(SyntaxNode Root, IReadOnlyList<ParsedMethod> Methods);
    private sealed record ParsedMethod(
        string Path,
        string PartitionKey,
        string TypeName,
        string Name,
        bool IsTest,
        bool IsStaticallySkipped,
        int StartLine,
        int EndLine,
        MethodDeclarationSyntax Syntax);
}
