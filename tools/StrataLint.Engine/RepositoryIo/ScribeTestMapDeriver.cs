using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.Engine;

internal enum TestMapUnknownReason
{
    VariablePath,
    DirectoryEnumeration,
    IndirectViaProductionLoader,
    MetadataUnavailable,
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
    bool IsStaticallySkipped = false,
    bool IsDiscoveryConditional = false)
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
    IReadOnlyList<MsBuildCompileFinding> CompileQueryFindings)
{
    internal IReadOnlyList<ScribeMetadataDegradation> MetadataDegradations { get; init; } = [];
}

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
        // 消化退出 CI 后,ci.yml 是仓内唯一的 workflow;守卫「无 workflow 代跑消化」
        // 与 lake 缓存契约都声明式读它(此前二者读的是已删除的 theory-ingest.yml)。
        ".github/workflows/ci.yml",
        ".lake/build/stratalint",
        "Blueprint",
        "CLAUDE.md",
        "D5",
        "D5/X_Frontier/ValuesProducer.lean",
        "Evidence",
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
        "docs/develop/theory",
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
                || file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal)
                || file.RelativePath.EndsWith("packages.lock.json", StringComparison.Ordinal))
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
                || file.Path.Value.EndsWith(".csproj", StringComparison.Ordinal)
                || file.Path.Value.EndsWith("packages.lock.json", StringComparison.Ordinal))
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
        .Where(static project => ScribeProjectCompilationContext.IsXunitProject(project.Content))
        .Select(static project => new ScribeTestProjectPartition(
            ProjectDirectory(project.Path),
            project.Path))
        .OrderBy(static partition => partition.Key, StringComparer.Ordinal)
        .ToArray();

    internal static IReadOnlyList<string> FindUnclassifiedManagedProjects(
        IEnumerable<(string Path, string Content)> projectFiles) => projectFiles
        .Where(static project => project.Path.StartsWith(ManagedTestProjectPrefix, StringComparison.Ordinal))
        .Where(project => !ScribeProjectCompilationContext.IsXunitProject(project.Content)
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

    internal static ScribeTestMap DeriveTracked(
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
        var compilationContext = ScribeProjectCompilationContext.Create(
            tracked,
            compileMap.ProjectBySourcePath,
            testProjects.Keys.ToHashSet(StringComparer.Ordinal));
        return DeriveSources(
            testSources,
            [],
            FindUnclassifiedManagedProjects(projectFiles),
            compileMap.Findings.Count == 0
                ? FindOrphanManagedSources(
                    sources.Select(static source => source.Path),
                    compileMap.ProjectBySourcePath)
                : [],
            FindDanglingCompileFailProofProjectExemptions(
                projectFiles.Select(static project => project.Path)),
            compileMap.ProjectBySourcePath,
            compileMap.Findings,
            compilationContext.ProductionAssemblies,
            compilationContext);
    }

    internal static ScribeTestMap DeriveSources(
        IEnumerable<TestMapSource> sourceFiles,
        IEnumerable<(string Path, int Line)> indirectProductionSites,
        IReadOnlyList<string>? unclassifiedManagedProjectPaths = null,
        IReadOnlyList<string>? orphanManagedSourcePaths = null,
        IReadOnlyList<string>? danglingCompileFailProofProjectExemptionPaths = null,
        IReadOnlyDictionary<string, string>? compileProjectBySourcePath = null,
        IReadOnlyList<MsBuildCompileFinding>? compileQueryFindings = null,
        IReadOnlySet<string>? productionAssemblies = null,
        ScribeProjectCompilationContext? compilationContext = null)
    {
        var parsed = ScribeTestSymbolBinder.Bind(
            sourceFiles,
            out var metadataDegradations,
            productionAssemblies,
            compilationContext).ToArray();
        var discoveryPaths = ExtractDiscoveryPaths(parsed);
        var methods = parsed.SelectMany(static source => source.Callables).ToArray();
        var indirect = indirectProductionSites.ToArray();
        var results = new List<ScribeTestMethod>();

        foreach (var test in methods.Where(static method => method.IsTest))
        {
            var paths = new HashSet<string>(StringComparer.Ordinal);
            var reasons = new HashSet<TestMapUnknownReason>();
            var pending = new Stack<ScribeBoundCallable>();
            var visited = new HashSet<ScribeBoundCallable>();
            pending.Push(test);
            while (pending.TryPop(out var method))
            {
                if (!visited.Add(method))
                {
                    continue;
                }

                InspectMethod(method, discoveryPaths, paths, reasons);
                reasons.UnionWith(method.BindingUnknownReasons);
                if (indirect.Any(site => site.Path == method.Path
                    && method.ContainsLine(site.Line)))
                {
                    reasons.Add(TestMapUnknownReason.IndirectViaProductionLoader);
                }

                foreach (var target in method.Targets)
                {
                    pending.Push(target);
                }
            }

            results.Add(new ScribeTestMethod(
                test.PartitionKey,
                test.Path,
                $"{test.TypeName}.{test.Name}",
                paths.Order(StringComparer.Ordinal).ToArray(),
                reasons.Order().ToArray(),
                test.IsStaticallySkipped,
                test.IsDiscoveryConditional));
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
            compileQueryFindings ?? [])
        {
            MetadataDegradations = metadataDegradations,
        };
    }

    private static void InspectMethod(
        ScribeBoundCallable method,
        IReadOnlyDictionary<string, IReadOnlyList<string>?> discoveryPaths,
        HashSet<string> paths,
        HashSet<TestMapUnknownReason> reasons)
    {
        var model = method.SemanticModel;
        foreach (var invocation in method.InspectionNodes.OfType<InvocationExpressionSyntax>())
        {
            if (IsAccessorCall(invocation, model, "Discover"))
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
            if (IsAccessorCall(invocation, model, "EnumerateDeclared"))
            {
                AddDeclaredPrefix(invocation, paths, reasons);
                continue;
            }

            if (IsAccessorCall(invocation, model, "EnumerateFiles"))
            {
                var enumerationArgument = invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression;
                if (enumerationArgument is not null
                    && ScribePathProvenance.IsNonRepository(
                        enumerationArgument,
                        model,
                        method.SemanticModels))
                {
                    continue;
                }
                reasons.Add(TestMapUnknownReason.DirectoryEnumeration);
                AddLiteralCreatePath(
                    enumerationArgument,
                    model,
                    paths,
                    reasons);
                continue;
            }

            if (!IsAccessorCall(
                    invocation,
                    model,
                    "ReadAllText",
                    "ReadAllBytes",
                    "FileExists",
                    "CopyTo"))
            {
                continue;
            }

            if (IsAccessorCall(invocation, model, "ReadAllText", "ReadAllBytes")
                && IsDeclaredEnumerationFullPath(
                    invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression,
                    model))
            {
                continue;
            }

            var argument = invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression;
            if (argument is not null
                && ScribePathProvenance.IsNonRepository(argument, model, method.SemanticModels))
            {
                continue;
            }

            AddLiteralCreatePath(
                argument,
                model,
                paths,
                reasons);
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

    private static bool IsDeclaredEnumerationFullPath(
        ExpressionSyntax? argument,
        SemanticModel model)
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
            if (IsAccessorCall(invocation, model, "EnumerateDeclared"))
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
        SemanticModel model,
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
        if (TryGetConstantString(expression, model, out var relativePath))
        {
            paths.Add(relativePath.Replace('\\', '/'));
            return;
        }

        if (TryGetCombinedRepositoryPath(argument, model, out relativePath))
        {
            paths.Add(relativePath);
            return;
        }

        reasons.Add(TestMapUnknownReason.VariablePath);
    }

    private static bool TryGetCombinedRepositoryPath(
        ExpressionSyntax? expression,
        SemanticModel model,
        out string path)
    {
        if (expression is InvocationExpressionSyntax combine
            && model.GetSymbolInfo(combine).Symbol is IMethodSymbol
            {
                Name: "Combine",
                ContainingType: { } pathType,
            }
            && pathType.ToDisplayString() == "System.IO.Path"
            && combine.ArgumentList.Arguments is { Count: >= 2 } arguments
            && ScribeTestSymbolBinder.IsRepositoryRootExpression(arguments[0].Expression, model))
        {
            var segments = new List<string>();
            foreach (var argument in arguments.Skip(1))
            {
                if (!TryGetConstantString(argument.Expression, model, out var segment))
                {
                    path = string.Empty;
                    return false;
                }
                segments.Add(segment);
            }

            path = string.Join('/', segments).Replace('\\', '/');
            return true;
        }

        path = string.Empty;
        return false;
    }

    private static bool TryGetConstantString(
        ExpressionSyntax? expression,
        SemanticModel model,
        out string value)
    {
        if (expression is not null
            && model.GetConstantValue(expression) is { HasValue: true, Value: string constant })
        {
            value = constant;
            return true;
        }

        value = string.Empty;
        return false;
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
        IEnumerable<ScribeParsedSource> sources)
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

    private static bool IsAccessorCall(
        InvocationExpressionSyntax invocation,
        SemanticModel model,
        params string[] names)
    {
        if (model.GetSymbolInfo(invocation).Symbol is not IMethodSymbol method
            || !names.Contains(method.Name, StringComparer.Ordinal))
        {
            return false;
        }

        if (!method.Locations.Any(static location => location.IsInSource))
        {
            var owner = method.ContainingType.ToDisplayString();
            return owner == "System.IO.File"
                || owner == "System.IO.Directory" && method.Name == "EnumerateFiles";
        }

        if (method.Name == "EnumerateDeclared"
            && method.Parameters.Length >= 2
            && method.Parameters[0].Type.SpecialType == SpecialType.System_String
            && method.Parameters[1].Type.SpecialType == SpecialType.System_String)
        {
            return true;
        }

        return IsRepositoryAccessorContract(method.ContainingType);
    }

    private static bool IsRepositoryAccessorContract(INamedTypeSymbol type) =>
        type.GetMembers().OfType<IPropertySymbol>().Any(static property =>
            property.Type.GetMembers().OfType<IPropertySymbol>().Any(static nested =>
                nested.Type.SpecialType == SpecialType.System_String
                && nested.Name == "FullPath"))
        && type.GetMembers().OfType<IMethodSymbol>().Any(method =>
            method.IsStatic
            && method.Name == "Discover"
            && SymbolEqualityComparer.Default.Equals(method.ReturnType, type));

}
