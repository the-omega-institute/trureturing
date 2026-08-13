using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal enum TestMapUnknownReason
{
    VariablePath,
    DirectoryEnumeration,
    IndirectViaProductionLoader,
    RepositoryRootMarker,
    Other,
}

internal sealed record TestMapSource(string Path, string Content);

internal sealed record ScribeTestMethod(
    string Id,
    IReadOnlyList<string> Paths,
    IReadOnlyList<TestMapUnknownReason> UnknownReasons)
{
    internal bool IsUnknown => UnknownReasons.Count != 0;
}

internal sealed record ScribeTestMap(IReadOnlyList<ScribeTestMethod> Methods)
{
    internal IReadOnlyList<ScribeTestMethod> Select(IEnumerable<string> changedPaths)
    {
        var changed = changedPaths.Select(Normalize).ToHashSet(StringComparer.Ordinal);
        return Methods.Where(method => method.IsUnknown || method.Paths.Any(declared =>
            changed.Any(path => path == declared
                || path.StartsWith(declared + "/", StringComparison.Ordinal)))).ToArray();
    }

    private static string Normalize(string path) => path.Replace('\\', '/').TrimStart('.', '/');
}

internal static class ScribeTestMapDeriver
{
    private const string ProjectPrefix = "tools/tests/StrataLint.Scribe.Tests/";

    internal static ScribeTestMap DeriveRepository(string repositoryRoot)
    {
        var sources = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => file.RelativePath.StartsWith(ProjectPrefix, StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .Select(file => new TestMapSource(file.RelativePath, File.ReadAllText(file.FullPath)))
            .ToArray();
        var indirectSites = ProductionRepositoryReadDeriver.InspectScribeTests(repositoryRoot)
            .Select(static site => (site.Path, site.Line))
            .ToArray();
        return DeriveSources(sources, indirectSites);
    }

    internal static ScribeTestMap DeriveSources(
        IEnumerable<TestMapSource> sourceFiles,
        IEnumerable<(string Path, int Line)> indirectProductionSites)
    {
        var parsed = sourceFiles.Select(Parse).ToArray();
        var discoveryPaths = ExtractDiscoveryPaths(parsed);
        var methods = parsed.SelectMany(static source => source.Methods).ToArray();
        var methodsByTypeAndName = methods.GroupBy(static method => (method.TypeName, method.Name))
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
                $"{test.TypeName}.{test.Name}",
                paths.Order(StringComparer.Ordinal).ToArray(),
                reasons.Order().ToArray()));
        }

        return new ScribeTestMap(results.OrderBy(static method => method.Id, StringComparer.Ordinal).ToArray());
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
        string TypeName,
        string Name,
        bool IsTest,
        int StartLine,
        int EndLine,
        MethodDeclarationSyntax Syntax);
}
