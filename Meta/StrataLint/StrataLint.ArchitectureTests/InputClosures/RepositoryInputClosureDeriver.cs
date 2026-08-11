using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal sealed record DerivedRepositoryEffect(
    string Project,
    string SourcePath,
    string Method,
    IReadOnlyList<string> Patterns);

internal sealed class RepositoryInputClosureResult : List<DerivedRepositoryEffect>
{
    internal List<string> DeclarationFindings { get; } = [];

    internal DerivedRepositoryEffect EffectFor(string method) =>
        this.Single(effect => string.Equals(effect.Method, method, StringComparison.Ordinal));
}

internal static class RepositoryInputClosureDeriver
{
    private const string AttributeName = "RepositoryReadPattern";

    internal static RepositoryInputClosureResult DeriveSynthetic(string source)
    {
        var tree = CSharpSyntaxTree.ParseText(source, path: "Synthetic.cs");
        return Derive(CSharpCompilation.Create(
            "InputClosureSynthetic",
            [tree],
            MetadataReferences(),
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary)),
            testMethodsOnly: true,
            repositoryRoot: null);
    }

    internal static RepositoryInputClosureResult DeriveRepository(string repositoryRoot) =>
        DeriveRepository(repositoryRoot, testMethodsOnly: false);

    private static RepositoryInputClosureResult DeriveRepository(
        string repositoryRoot,
        bool testMethodsOnly)
    {
        var trees = CSharpRepositorySources.Enumerate(repositoryRoot)
            .Select(source => CSharpSyntaxTree.ParseText(
                File.ReadAllText(source.FullPath),
                path: source.RelativePath))
            .ToArray();
        return Derive(CSharpCompilation.Create(
            "InputClosureRepository",
            trees,
            MetadataReferences(),
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary)),
            testMethodsOnly,
            repositoryRoot);
    }

    internal static RepositoryInputClosureResult DeriveRepositoryTests(string repositoryRoot)
    {
        var result = DeriveRepository(repositoryRoot, testMethodsOnly: true);
        result.RemoveAll(effect => !effect.Project.EndsWith("Tests", StringComparison.Ordinal)
            || effect.Project == "Unknown"
            || !effect.SourcePath.StartsWith("Meta/StrataLint/", StringComparison.Ordinal));
        return result;
    }

    private static RepositoryInputClosureResult Derive(
        CSharpCompilation compilation,
        bool testMethodsOnly,
        string? repositoryRoot)
    {
        var result = new RepositoryInputClosureResult();
        var methods = compilation.SyntaxTrees
            .SelectMany(tree => tree.GetRoot().DescendantNodes()
                .OfType<BaseMethodDeclarationSyntax>()
                .Select(node => (Node: node, Model: compilation.GetSemanticModel(tree))))
            .Select(item => (item.Node, item.Model, Symbol: item.Model.GetDeclaredSymbol(item.Node)))
            .Where(static item => item.Symbol is not null)
            .Select(static item => (item.Node, item.Model, Symbol: item.Symbol!))
            .ToArray();
        var declarations = methods.ToDictionary(
            static item => (ISymbol)item.Symbol,
            static item => (item.Node, item.Model),
            SymbolEqualityComparer.Default);

        foreach (var item in methods.Where(item =>
                     !testMethodsOnly || IsTestMethod(item.Node)))
        {
            var patterns = DeriveMethod(
                item.Symbol!,
                declarations,
                result.DeclarationFindings,
                []);
            var sourcePath = item.Node.SyntaxTree.FilePath.Replace('\\', '/');
            if (repositoryRoot is not null && Path.IsPathRooted(sourcePath))
            {
                sourcePath = Path.GetRelativePath(repositoryRoot, sourcePath).Replace('\\', '/');
            }
            result.Add(new DerivedRepositoryEffect(
                ProjectName(sourcePath),
                sourcePath,
                DisplayName(item.Symbol!),
                patterns.Order(StringComparer.Ordinal).ToArray()));
        }

        return result;
    }

    private static HashSet<string> DeriveMethod(
        IMethodSymbol method,
        IReadOnlyDictionary<ISymbol, (BaseMethodDeclarationSyntax Node, SemanticModel Model)> declarations,
        List<string> findings,
        HashSet<IMethodSymbol> visiting)
    {
        if (!visiting.Add(method))
        {
            return ["All"];
        }

        if (!declarations.TryGetValue(method, out var declaration))
        {
            return ["All"];
        }

        var declared = ParsePatterns(declaration.Node, declaration.Model, findings);
        if (declared.Count > 0)
        {
            if (!ValidateDeclaredReads(declaration.Node, declaration.Model, declared, findings))
            {
                return ["All"];
            }

            return declared;
        }

        var result = new HashSet<string>(StringComparer.Ordinal);
        foreach (var invocation in declaration.Node.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            var target = declaration.Model.GetSymbolInfo(invocation).Symbol as IMethodSymbol;
            if (target is null || IsUnknownExternal(target))
            {
                return ["All"];
            }

            if (declarations.ContainsKey(target.OriginalDefinition))
            {
                result.UnionWith(DeriveMethod(
                    target.OriginalDefinition,
                    declarations,
                    findings,
                    new HashSet<IMethodSymbol>(visiting, SymbolEqualityComparer.Default)));
            }
        }

        foreach (var creation in declaration.Node.DescendantNodes().OfType<ObjectCreationExpressionSyntax>())
        {
            var target = declaration.Model.GetSymbolInfo(creation).Symbol as IMethodSymbol;
            if (target is null)
            {
                return ["All"];
            }

            if (declarations.ContainsKey(target.OriginalDefinition))
            {
                result.UnionWith(DeriveMethod(
                    target.OriginalDefinition,
                    declarations,
                    findings,
                    new HashSet<IMethodSymbol>(visiting, SymbolEqualityComparer.Default)));
            }
        }

        return result.Count == 0 || result.Contains("All") ? ["All"] : result;
    }

    private static HashSet<string> ParsePatterns(
        BaseMethodDeclarationSyntax method,
        SemanticModel model,
        List<string> findings)
    {
        var result = new HashSet<string>(StringComparer.Ordinal);
        foreach (var attribute in method.AttributeLists.SelectMany(static list => list.Attributes)
                     .Where(attribute => attribute.Name.ToString().Contains(AttributeName, StringComparison.Ordinal)))
        {
            var arguments = attribute.ArgumentList?.Arguments;
            if (arguments is null || arguments.Value.Count == 0)
            {
                findings.Add($"{method.SyntaxTree.FilePath}: read pattern has no kind");
                continue;
            }

            var kind = arguments.Value[0].Expression.ToString().Split('.').Last();
            if (kind == "All" && arguments.Value.Count == 1)
            {
                result.Add("All");
                continue;
            }

            var path = arguments.Value.Count > 1
                ? model.GetConstantValue(arguments.Value[1].Expression)
                : default;
            if (kind is not ("Exact" or "Subtree") || !path.HasValue || path.Value is not string text
                || string.IsNullOrWhiteSpace(text))
            {
                findings.Add($"{method.SyntaxTree.FilePath}: read pattern is not parseable");
                continue;
            }

            result.Add($"{kind}({text})");
        }

        return result;
    }

    private static bool ValidateDeclaredReads(
        BaseMethodDeclarationSyntax method,
        SemanticModel model,
        HashSet<string> patterns,
        List<string> findings)
    {
        var exactPaths = patterns
            .Where(static pattern => pattern.StartsWith("Exact(", StringComparison.Ordinal))
            .Select(static pattern => pattern[6..^1])
            .ToArray();
        if (exactPaths.Length == 0)
        {
            return true;
        }

        foreach (var invocation in method.DescendantNodes().OfType<InvocationExpressionSyntax>())
        {
            var target = model.GetSymbolInfo(invocation).Symbol as IMethodSymbol;
            if (target?.ContainingType.ToDisplayString() != "System.IO.File"
                || !target.Name.StartsWith("Read", StringComparison.Ordinal))
            {
                continue;
            }

            var argument = invocation.ArgumentList.Arguments.FirstOrDefault()?.Expression;
            if (argument is null || !exactPaths.Any(path => ExpressionNamesConstant(argument, model, path)))
            {
                findings.Add($"{method.SyntaxTree.FilePath}: cannot prove Exact for repository read");
                return false;
            }
        }

        return true;
    }

    private static bool ExpressionNamesConstant(ExpressionSyntax expression, SemanticModel model, string expected) =>
        expression.DescendantNodesAndSelf().OfType<ExpressionSyntax>().Any(node =>
        {
            var constant = model.GetConstantValue(node);
            return constant.HasValue && string.Equals(constant.Value as string, expected, StringComparison.Ordinal);
        });

    private static bool IsUnknownExternal(IMethodSymbol method)
    {
        var type = method.ContainingType.ToDisplayString();
        return type is "System.Diagnostics.Process" or "System.Reflection.Assembly"
            || method.ContainingType.TypeKind == TypeKind.Dynamic;
    }

    private static bool IsTestMethod(BaseMethodDeclarationSyntax method) =>
        method.AttributeLists.SelectMany(static list => list.Attributes).Any(attribute =>
            attribute.Name.ToString() is "Fact" or "FactAttribute" or "Theory" or "TheoryAttribute");

    private static string DisplayName(IMethodSymbol method)
    {
        var type = method.ContainingType.ToDisplayString();
        return method.MethodKind == MethodKind.Constructor
            ? type + "..ctor"
            : type + "." + method.Name;
    }

    private static string ProjectName(string sourcePath)
    {
        const string prefix = "Meta/StrataLint/";
        if (!sourcePath.StartsWith(prefix, StringComparison.Ordinal))
        {
            return "Synthetic";
        }

        var remainder = sourcePath[prefix.Length..];
        var slash = remainder.IndexOf('/');
        return slash < 0 ? "Unknown" : remainder[..slash];
    }

    private static IEnumerable<MetadataReference> MetadataReferences()
    {
        var paths = ((string?)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES"))!
            .Split(Path.PathSeparator)
            .Concat(AppDomain.CurrentDomain.GetAssemblies()
                .Where(static assembly => !assembly.IsDynamic && !string.IsNullOrEmpty(assembly.Location))
                .Select(static assembly => assembly.Location))
            .Distinct(StringComparer.Ordinal);
        return paths.Select(static path => MetadataReference.CreateFromFile(path));
    }

}
