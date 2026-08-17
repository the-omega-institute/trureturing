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
    IReadOnlyList<string> UnclassifiedManagedProjectPaths);

internal sealed record ScribeTestProjectPartition(string Key, string Prefix);

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

    private static readonly IReadOnlySet<string> PinnedCompileFailProofProjectExemptionBaseline =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj",
            "tools/tests/CompileFailProof/CompileFailProof.csproj",
        };

    // This is the read surface used by the engineering path-filter guard. Entries are either
    // exact files or directory roots; adding a new repository read requires updating
    // this declaration and its review-visible guard.
    internal static readonly IReadOnlyList<string> DeclaredPathWhitelist =
    [
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
        "tools",
        "tools/tests/StrataLint.ArchitectureTests",
        "tools/tests/StrataLint.Scribe.Tests",
        "tools/tests/StrataLint.Tests",
        "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml",
    ];

    internal static bool IsDeclaredPathAllowed(string path) =>
        DeclaredPathWhitelist.Any(allowed => path == allowed
            || path.StartsWith(allowed + "/", StringComparison.Ordinal));

    internal static ScribeTestMap DeriveRepository(string repositoryRoot)
    {
        var files = GitIndexRepositoryFiles.Enumerate(repositoryRoot);
        var projectFiles = files
            .Where(static file => file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(file => (file.RelativePath, File.ReadAllText(file.FullPath)))
            .ToArray();
        var partitions = DeriveProjectPartitions(projectFiles);
        var unclassifiedProjects = FindUnclassifiedManagedProjects(projectFiles);
        var sources = files
            .Where(file => file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
                && TryPartition(file.RelativePath, partitions, out _))
            .Select(file => new TestMapSource(
                file.RelativePath,
                File.ReadAllText(file.FullPath),
                PartitionFor(file.RelativePath, partitions).Key))
            .ToArray();
        var productionSources = files
            .Where(static file => IsProductionSource(file.RelativePath))
            .Select(file => new RepositoryReadSource(
                ProjectName(file.RelativePath),
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .ToArray();
        var indirectSites = ProductionRepositoryReadDeriver.InspectTests(productionSources, sources)
            .Select(static site => (site.Path, site.Line))
            .ToArray();
        return DeriveSources(sources, indirectSites, unclassifiedProjects);
    }

    internal static ScribeTestMap DeriveSnapshot(RepositorySnapshot snapshot)
    {
        var projectFiles = snapshot.Files.Values
            .Where(static file => file.Path.Value.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(static file => (file.Path.Value, file.Text))
            .ToArray();
        var partitions = DeriveProjectPartitions(projectFiles);
        var unclassifiedProjects = FindUnclassifiedManagedProjects(projectFiles);
        var sources = snapshot.Files.Values
            .Where(file => file.Path.Value.EndsWith(".cs", StringComparison.Ordinal)
                && TryPartition(file.Path.Value, partitions, out _))
            .Select(file => new TestMapSource(
                file.Path.Value,
                file.Text,
                PartitionFor(file.Path.Value, partitions).Key))
            .ToArray();
        var productionSources = snapshot.Files.Values
            .Where(static file => IsProductionSource(file.Path.Value))
            .Select(static file => new RepositoryReadSource(
                ProjectName(file.Path.Value),
                file.Path.Value,
                file.Text))
            .ToArray();
        var indirectSites = ProductionRepositoryReadDeriver.InspectTests(productionSources, sources)
            .Select(static site => (site.Path, site.Line))
            .ToArray();
        return DeriveSources(sources, indirectSites, unclassifiedProjects);
    }

    internal static IReadOnlyList<ScribeTestProjectPartition> DeriveProjectPartitions(
        IEnumerable<(string Path, string Content)> projectFiles) => projectFiles
        .Where(static project => IsXunitProject(project.Content))
        .Select(static project =>
        {
            var slash = project.Path.LastIndexOf('/');
            var key = slash < 0 ? "." : project.Path[..slash];
            return new ScribeTestProjectPartition(key, key + "/");
        })
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

    internal static IReadOnlyList<string> FindAddedCompileFailProofProjectExemptions(
        IEnumerable<string> exemptions) => exemptions
        .Except(PinnedCompileFailProofProjectExemptionBaseline, StringComparer.Ordinal)
        .Order(StringComparer.Ordinal)
        .ToArray();

    internal static ScribeTestMap DeriveSources(
        IEnumerable<TestMapSource> sourceFiles,
        IEnumerable<(string Path, int Line)> indirectProductionSites,
        IReadOnlyList<string>? unclassifiedManagedProjectPaths = null)
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
            unclassifiedManagedProjectPaths ?? []);
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

    private static bool TryPartition(
        string path,
        IReadOnlyList<ScribeTestProjectPartition> partitions,
        out ScribeTestProjectPartition? partition)
    {
        partition = partitions
            .Where(item => path.StartsWith(item.Prefix, StringComparison.Ordinal))
            .OrderByDescending(static item => item.Prefix.Length)
            .FirstOrDefault();
        return partition is not null;
    }

    private static ScribeTestProjectPartition PartitionFor(
        string path,
        IReadOnlyList<ScribeTestProjectPartition> partitions) =>
        TryPartition(path, partitions, out var partition)
            ? partition!
            : throw new InvalidOperationException($"test source {path} has no xUnit project partition");

    private static bool IsProductionSource(string path) =>
        path.StartsWith("tools/StrataLint.", StringComparison.Ordinal)
        && path.EndsWith(".cs", StringComparison.Ordinal)
        && !path.Contains(".Tests/", StringComparison.Ordinal);

    private static string ProjectName(string path)
    {
        var slash = path.IndexOf('/', "tools/".Length);
        return path["tools/".Length..slash];
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
        }
        else
        {
            reasons.Add(TestMapUnknownReason.VariablePath);
        }
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
        && (member.Expression.ToString().Contains("RepositoryAccessor", StringComparison.Ordinal)
            || member.Expression is IdentifierNameSyntax
            || member.Expression is MemberAccessExpressionSyntax
            || member.Expression is InvocationExpressionSyntax);

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
