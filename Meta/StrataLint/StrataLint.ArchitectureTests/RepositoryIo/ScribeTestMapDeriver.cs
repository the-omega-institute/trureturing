using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal enum TestMapUnknownReason
{
    VariablePath,
    DirectoryEnumeration,
    IndirectViaProductionLoader,
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
    private const string ProjectPrefix = "Meta/StrataLint/StrataLint.Scribe.Tests/";

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

                InspectMethod(method, paths, reasons);
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
        HashSet<string> paths,
        HashSet<TestMapUnknownReason> reasons)
    {
        foreach (var invocation in method.Syntax.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            if (IsAccessorCall(invocation, "Discover"))
            {
                AddDiscoveryPaths(invocation, paths, reasons);
            }

            if (IsAccessorCall(invocation, "EnumerateFiles"))
            {
                reasons.Add(TestMapUnknownReason.DirectoryEnumeration);
                continue;
            }

            if (!IsAccessorCall(invocation, "ReadAllText", "ReadAllBytes", "FileExists", "CopyTo"))
            {
                continue;
            }

            var create = invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression
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
    }

    private static void AddDiscoveryPaths(
        InvocationExpressionSyntax invocation,
        HashSet<string> paths,
        HashSet<TestMapUnknownReason> reasons)
    {
        var criterion = invocation.ArgumentList.Arguments.LastOrDefault()?.Expression
            as MemberAccessExpressionSyntax;
        switch (criterion?.Name.Identifier.ValueText)
        {
            case "GlobalJsonAndBlueprintDirectoryNotFound":
            case "GlobalJsonAndBlueprintInvalidOperation":
                paths.Add("global.json");
                paths.Add("Blueprint");
                break;
            case "GlobalJsonAndLibraryInvalidOperation":
                paths.Add("global.json");
                paths.Add("Library");
                break;
            case "ClaudeDirectoryNotFound": paths.Add("CLAUDE.md"); break;
            case "LakefileInvalidOperation": paths.Add("lakefile.toml"); break;
            case "FileMapDirectoryNotFound": paths.Add("Meta/FILEMAP.toml"); break;
            case "ValuesDataDirectoryNotFound": paths.Add("Golden/values-kernels.toml"); break;
            case "ValuesProducerDirectoryNotFound": paths.Add("D5/X_Frontier/ValuesProducer.lean"); break;
            default: reasons.Add(TestMapUnknownReason.Other); break;
        }
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
        return new ParsedSource(methods);
    }

    private sealed record ParsedSource(IReadOnlyList<ParsedMethod> Methods);
    private sealed record ParsedMethod(
        string Path,
        string TypeName,
        string Name,
        bool IsTest,
        int StartLine,
        int EndLine,
        MethodDeclarationSyntax Syntax);
}
