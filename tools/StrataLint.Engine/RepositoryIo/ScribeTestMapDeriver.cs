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
    IReadOnlyList<TestMapUnknownReason> UnknownReasons)
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

    // #3649: the determinism ban is only as strong as the set of projects it is attached to.
    // PR #3612 withdrew a failed content-scanning criterion and, in the same change, removed the
    // meta-test that guarded *project-set completeness*. Those are two different things; this is
    // the second one, restored on its own terms.
    //
    // What this decides: every xUnit verdict project under tools/tests/ must carry BOTH the
    // BannedApiAnalyzers package reference AND the BannedSymbols.Determinism.txt AdditionalFiles
    // entry, and must not suppress RS0030 via NoWarn. Non-xUnit projects are out of scope; the two
    // compile-fail-proof projects have their own governed class (CompileFailProofProjectExemptions).
    //
    // What this does NOT decide (the reflexive half of the reject-set, stated because a guard that
    // does not name its own gaps is worse than none):
    //   * `#pragma warning disable RS0030` inside a source file — that is a per-file suppression
    //     this predicate cannot see; it reads project files only.
    //   * `.editorconfig` severity downgrades.
    //   * a `PackageReference` or `AdditionalFiles` made inert by a false `Condition`.
    // Those three are the "can the check itself be skipped" dimension; they remain review-guarded.
    internal static IReadOnlyList<string> FindVerdictProjectsMissingDeterminismBan(
        IEnumerable<(string Path, string Content)> projectFiles) => projectFiles
        .Where(static project => project.Path.StartsWith(ManagedTestProjectPrefix, StringComparison.Ordinal))
        .Where(static project => IsXunitProject(project.Content))
        .Where(static project => !HasDeterminismBanWiring(project.Content))
        .Select(static project => project.Path)
        .Order(StringComparer.Ordinal)
        .ToArray();

    internal static IReadOnlyList<string> FindVerdictProjectsMissingDeterminismBan(
        string repositoryRoot) =>
        FindVerdictProjectsMissingDeterminismBan(
            GitIndexRepositoryFiles.Enumerate(repositoryRoot)
                .Where(static file => file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
                .Select(static file => (file.RelativePath, File.ReadAllText(file.FullPath))));

    private static bool HasDeterminismBanWiring(string projectContent) =>
        projectContent.Contains("BannedSymbols.Determinism", StringComparison.Ordinal)
        && projectContent.Contains("BannedApiAnalyzers", StringComparison.Ordinal)
        && !SuppressesDeterminismDiagnostic(projectContent);

    private static bool SuppressesDeterminismDiagnostic(string projectContent) =>
        projectContent
            .Split('\n')
            .Where(static line => line.Contains("NoWarn", StringComparison.Ordinal))
            .Any(static line => line.Contains("RS0030", StringComparison.Ordinal));

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
                reasons.Order().ToArray()));
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

            AddLiteralCreatePath(invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression, paths, reasons);
        }
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
                method.AttributeLists.SelectMany(static list => list.Attributes)
                    .Any(static attribute => attribute.Name.ToString() is "Fact" or "FactAttribute" or "Theory" or "TheoryAttribute"),
                span.StartLinePosition.Line + 1,
                span.EndLinePosition.Line + 1,
                method);
        }).ToArray();
        return new ParsedSource(root, methods);
    }

    private sealed record ParsedSource(SyntaxNode Root, IReadOnlyList<ParsedMethod> Methods);
    private sealed record ParsedMethod(
        string Path,
        string PartitionKey,
        string TypeName,
        string Name,
        bool IsTest,
        int StartLine,
        int EndLine,
        MethodDeclarationSyntax Syntax);
}
