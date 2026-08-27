using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal sealed class ProductionSourceGraph
{
    private static readonly string[] ProductionPrefixes =
    [
        "tools/StrataLint.Cli/",
        "tools/StrataLint.Engine/",
        "tools/StrataLint.Scribe/",
        "tools/Trureturing.Truth/",
    ];

    private readonly CSharpCompilation compilation;
    private readonly IReadOnlyDictionary<SyntaxTree, string> paths;
    private readonly Dictionary<IMethodSymbol, SyntaxNode> declarations;
    private readonly Dictionary<IFieldSymbol, SyntaxNode> fieldInitializers;
    private readonly Dictionary<IPropertySymbol, SyntaxNode> propertyInitializers;
    private readonly ImmutableArray<IMethodSymbol> sourceMethods;

    private ProductionSourceGraph(
        CSharpCompilation compilation,
        IReadOnlyDictionary<SyntaxTree, string> paths,
        Dictionary<IMethodSymbol, SyntaxNode> declarations,
        Dictionary<IFieldSymbol, SyntaxNode> fieldInitializers,
        Dictionary<IPropertySymbol, SyntaxNode> propertyInitializers)
    {
        this.compilation = compilation;
        this.paths = paths;
        this.declarations = declarations;
        this.fieldInitializers = fieldInitializers;
        this.propertyInitializers = propertyInitializers;
        sourceMethods = declarations.Keys.ToImmutableArray();
    }

    internal static ProductionSourceGraph Create(string repositoryRoot)
    {
        var sources = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => IsProductionPath(file.RelativePath)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .Select(file => (
                file.RelativePath,
                Tree: CSharpSyntaxTree.ParseText(
                    File.ReadAllText(file.FullPath),
                    CSharpParseOptions.Default.WithLanguageVersion(LanguageVersion.Preview),
                    file.RelativePath)))
            .ToArray();
        var compilation = CSharpCompilation.Create(
            "ProductionReachability",
            sources.Select(static source => source.Tree).Append(ImplicitUsingsTree()),
            PlatformReferences(),
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
        var paths = sources.ToDictionary(
            static source => (SyntaxTree)source.Tree,
            static source => source.RelativePath);
        var declarations = new Dictionary<IMethodSymbol, SyntaxNode>(SymbolEqualityComparer.Default);
        var fieldInitializers = new Dictionary<IFieldSymbol, SyntaxNode>(SymbolEqualityComparer.Default);
        var propertyInitializers = new Dictionary<IPropertySymbol, SyntaxNode>(SymbolEqualityComparer.Default);

        foreach (var source in sources)
        {
            var model = compilation.GetSemanticModel(source.Tree);
            var root = source.Tree.GetRoot();
            foreach (var declaration in root.DescendantNodes().OfType<BaseMethodDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(declaration) is IMethodSymbol method)
                {
                    declarations[Normalize(method)] = declaration;
                }
            }
            foreach (var declaration in root.DescendantNodes().OfType<AccessorDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(declaration) is IMethodSymbol method)
                {
                    declarations[Normalize(method)] = declaration;
                }
            }
            foreach (var declaration in root.DescendantNodes().OfType<LocalFunctionStatementSyntax>())
            {
                if (model.GetDeclaredSymbol(declaration) is IMethodSymbol method)
                {
                    declarations[Normalize(method)] = declaration;
                }
            }
            foreach (var variable in root.DescendantNodes().OfType<VariableDeclaratorSyntax>()
                .Where(static variable => variable.Initializer is not null))
            {
                if (model.GetDeclaredSymbol(variable) is IFieldSymbol field)
                {
                    fieldInitializers[field.OriginalDefinition] = variable.Initializer!.Value;
                }
            }
            foreach (var property in root.DescendantNodes().OfType<PropertyDeclarationSyntax>()
                .Where(static property => property.Initializer is not null))
            {
                if (model.GetDeclaredSymbol(property) is IPropertySymbol symbol)
                {
                    propertyInitializers[symbol.OriginalDefinition] = property.Initializer!.Value;
                }
            }
        }

        return new ProductionSourceGraph(
            compilation,
            paths,
            declarations,
            fieldInitializers,
            propertyInitializers);
    }

    internal IReadOnlyList<string> ReachableFrom(string entryPoint)
    {
        var entry = declarations.Keys.Single(method => Display(method) == entryPoint);
        var pending = new Queue<ISymbol>();
        var visited = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        pending.Enqueue(entry);
        while (pending.TryDequeue(out var symbol))
        {
            symbol = Normalize(symbol);
            if (!visited.Add(symbol))
            {
                continue;
            }

            switch (symbol)
            {
                case IMethodSymbol method:
                    AddDispatchTargets(method, pending);
                    if (declarations.TryGetValue(method, out var declaration))
                    {
                        AddDependencies(declaration, pending);
                    }
                    break;
                case IFieldSymbol field when fieldInitializers.TryGetValue(field, out var initializer):
                    AddDependencies(initializer, pending);
                    break;
                case IPropertySymbol property:
                    if (property.GetMethod is not null) pending.Enqueue(property.GetMethod);
                    if (property.SetMethod is not null) pending.Enqueue(property.SetMethod);
                    if (propertyInitializers.TryGetValue(property, out var propertyInitializer))
                    {
                        AddDependencies(propertyInitializer, pending);
                    }
                    break;
            }
        }

        return visited
            .SelectMany(static symbol => symbol switch
            {
                IMethodSymbol method => new[] { Display(method), Display(method.ContainingType) },
                INamedTypeSymbol type => new[] { Display(type) },
                _ => Array.Empty<string>(),
            })
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    internal IReadOnlyList<string> MethodDefinitionsNamed(string name) => declarations.Keys
        .Where(method => string.Equals(method.Name, name, StringComparison.Ordinal))
        .Select(Display)
        .Order(StringComparer.Ordinal)
        .ToArray();

    internal IReadOnlyList<string> ProductionReferencePaths(string methodDisplay)
    {
        var target = declarations.Keys.Single(method => Display(method) == methodDisplay);
        var result = new HashSet<string>(StringComparer.Ordinal);
        foreach (var tree in paths.Keys)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var invocation in tree.GetRoot().DescendantNodes().OfType<InvocationExpressionSyntax>())
            {
                if (BoundMethods(model, invocation).Any(method =>
                    SymbolEqualityComparer.Default.Equals(Normalize(method), target)))
                {
                    result.Add(paths[tree]);
                }
            }
        }
        return result.Order(StringComparer.Ordinal).ToArray();
    }

    private void AddDependencies(SyntaxNode node, Queue<ISymbol> pending)
    {
        var model = compilation.GetSemanticModel(node.SyntaxTree);
        foreach (var invocation in node.DescendantNodesAndSelf().OfType<InvocationExpressionSyntax>())
        {
            foreach (var method in BoundMethods(model, invocation)) pending.Enqueue(method);
        }
        foreach (var creation in node.DescendantNodesAndSelf().OfType<ObjectCreationExpressionSyntax>())
        {
            foreach (var method in BoundMethods(model, creation)) pending.Enqueue(method);
        }
        foreach (var name in node.DescendantNodesAndSelf().OfType<SimpleNameSyntax>())
        {
            var info = model.GetSymbolInfo(name);
            foreach (var symbol in Symbols(info))
            {
                switch (symbol)
                {
                    case IFieldSymbol field:
                        pending.Enqueue(field.OriginalDefinition);
                        break;
                    case IPropertySymbol property:
                        pending.Enqueue(property.OriginalDefinition);
                        break;
                    case IMethodSymbol method when model.GetTypeInfo(name).ConvertedType?.TypeKind == TypeKind.Delegate:
                        pending.Enqueue(method);
                        break;
                }
            }
        }
    }

    private void AddDispatchTargets(IMethodSymbol target, Queue<ISymbol> pending)
    {
        if (target.ContainingType.TypeKind == TypeKind.Interface)
        {
            foreach (var method in sourceMethods.Where(method => method.ContainingType.AllInterfaces.Any(
                @interface => SymbolEqualityComparer.Default.Equals(
                    @interface.OriginalDefinition,
                    target.ContainingType.OriginalDefinition))))
            {
                var implementation = method.ContainingType.FindImplementationForInterfaceMember(target);
                if (implementation is IMethodSymbol implemented
                    && SymbolEqualityComparer.Default.Equals(Normalize(implemented), method))
                {
                    pending.Enqueue(method);
                }
            }
        }
        if (target.IsVirtual || target.IsAbstract || target.IsOverride)
        {
            foreach (var method in sourceMethods.Where(method => Overrides(method, target)))
            {
                pending.Enqueue(method);
            }
        }
    }

    private static bool Overrides(IMethodSymbol method, IMethodSymbol target)
    {
        for (var current = method.OverriddenMethod; current is not null; current = current.OverriddenMethod)
        {
            if (SymbolEqualityComparer.Default.Equals(Normalize(current), Normalize(target))) return true;
        }
        return false;
    }

    private static IEnumerable<IMethodSymbol> BoundMethods(SemanticModel model, SyntaxNode node) =>
        Symbols(model.GetSymbolInfo(node)).OfType<IMethodSymbol>();

    private static IEnumerable<ISymbol> Symbols(SymbolInfo info)
    {
        if (info.Symbol is not null) yield return info.Symbol;
        foreach (var candidate in info.CandidateSymbols) yield return candidate;
    }

    private static ISymbol Normalize(ISymbol symbol) => symbol switch
    {
        IMethodSymbol method => Normalize(method),
        IFieldSymbol field => field.OriginalDefinition,
        IPropertySymbol property => property.OriginalDefinition,
        INamedTypeSymbol type => type.OriginalDefinition,
        _ => symbol,
    };

    private static IMethodSymbol Normalize(IMethodSymbol method) =>
        (method.ReducedFrom ?? method).OriginalDefinition;

    private static string Display(ISymbol symbol) =>
        symbol.ToDisplayString(SymbolDisplayFormat.CSharpErrorMessageFormat);

    private static bool IsProductionPath(string path) =>
        ProductionPrefixes.Any(prefix => path.StartsWith(prefix, StringComparison.Ordinal));

    private static IEnumerable<MetadataReference> PlatformReferences()
    {
        var runtimePaths = AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") as string
            ?? throw new InvalidOperationException("runtime platform assemblies are unavailable");
        return runtimePaths.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Distinct(StringComparer.Ordinal)
            .Select(static path => MetadataReference.CreateFromFile(path));
    }

    private static SyntaxTree ImplicitUsingsTree() => CSharpSyntaxTree.ParseText(
        """
        global using System;
        global using System.Collections.Generic;
        global using System.Collections.Immutable;
        global using System.IO;
        global using System.Linq;
        global using System.Net.Http;
        global using System.Threading;
        global using System.Threading.Tasks;
        """,
        CSharpParseOptions.Default.WithLanguageVersion(LanguageVersion.Preview),
        "ImplicitUsings.g.cs");
}
