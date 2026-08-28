using System.Collections.Immutable;
using System.Xml.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal sealed class ProductionSourceGraph
{
    private readonly CSharpCompilation compilation;
    private readonly IReadOnlyDictionary<SyntaxTree, string> paths;
    private readonly Dictionary<IMethodSymbol, SyntaxNode> declarations;
    private readonly Dictionary<IFieldSymbol, SyntaxNode> fieldInitializers;
    private readonly Dictionary<IPropertySymbol, SyntaxNode> propertyInitializers;
    private readonly ImmutableArray<IMethodSymbol> sourceMethods;
    private readonly ImmutableArray<(string Description, IMethodSymbol Method)> executableMethodRoots;
    private readonly ImmutableArray<(string Description, SyntaxNode Statement)> executableTopLevelRoots;

    private ProductionSourceGraph(
        CSharpCompilation compilation,
        IReadOnlyDictionary<SyntaxTree, string> paths,
        Dictionary<IMethodSymbol, SyntaxNode> declarations,
        Dictionary<IFieldSymbol, SyntaxNode> fieldInitializers,
        Dictionary<IPropertySymbol, SyntaxNode> propertyInitializers,
        ImmutableArray<(string Description, IMethodSymbol Method)> executableMethodRoots,
        ImmutableArray<(string Description, SyntaxNode Statement)> executableTopLevelRoots)
    {
        this.compilation = compilation;
        this.paths = paths;
        this.declarations = declarations;
        this.fieldInitializers = fieldInitializers;
        this.propertyInitializers = propertyInitializers;
        this.executableMethodRoots = executableMethodRoots;
        this.executableTopLevelRoots = executableTopLevelRoots;
        sourceMethods = declarations.Keys.ToImmutableArray();
    }

    internal static ProductionSourceGraph Create(string repositoryRoot)
    {
        var repositoryFiles = GitIndexRepositoryFiles.Enumerate(repositoryRoot);
        var projects = LoadProductionProjects(repositoryFiles);
        var sources = repositoryFiles
            .Where(file => projects.Any(project => project.Includes(file.RelativePath))
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

        var executableMethodRoots = ImmutableArray.CreateBuilder<(string, IMethodSymbol)>();
        var executableTopLevelRoots = ImmutableArray.CreateBuilder<(string, SyntaxNode)>();
        foreach (var project in projects.Where(static project => project.IsExecutable))
        {
            var projectMethods = declarations
                .Where(item => item.Key is { Name: "Main", IsStatic: true, MethodKind: MethodKind.Ordinary }
                    && project.Includes(paths[item.Value.SyntaxTree]))
                .OrderBy(static item => Display(item.Key), StringComparer.Ordinal)
                .ToArray();
            var projectTopLevel = sources
                .Where(source => project.Includes(source.RelativePath))
                .SelectMany(source => source.Tree.GetRoot()
                    .DescendantNodes()
                    .OfType<GlobalStatementSyntax>()
                    .Select(statement => (source.RelativePath, Statement: (SyntaxNode)statement)))
                .OrderBy(static item => item.RelativePath, StringComparer.Ordinal)
                .ThenBy(static item => item.Statement.SpanStart)
                .ToArray();
            if (projectMethods.Length == 0 && projectTopLevel.Length == 0)
            {
                throw new InvalidOperationException(
                    $"tracked executable project has no discovered C# entry point: {project.RelativePath}");
            }

            foreach (var item in projectMethods)
            {
                executableMethodRoots.Add(($"{project.RelativePath}::{Display(item.Key)}", item.Key));
            }
            foreach (var item in projectTopLevel)
            {
                executableTopLevelRoots.Add((
                    $"{project.RelativePath}::top-level:{item.RelativePath}",
                    item.Statement));
            }
        }

        return new ProductionSourceGraph(
            compilation,
            paths,
            declarations,
            fieldInitializers,
            propertyInitializers,
            executableMethodRoots.ToImmutable(),
            executableTopLevelRoots.ToImmutable());
    }

    internal IReadOnlyList<string> ExecutableEntryPointDescriptions => executableMethodRoots
        .Select(static root => root.Description)
        .Concat(executableTopLevelRoots.Select(static root => root.Description))
        .Distinct(StringComparer.Ordinal)
        .Order(StringComparer.Ordinal)
        .ToArray();

    internal IReadOnlyList<string> ReachableFromExecutableEntryPoints()
    {
        var pending = new Queue<ISymbol>();
        var visited = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        foreach (var root in executableMethodRoots) pending.Enqueue(root.Method);
        foreach (var root in executableTopLevelRoots) AddDependencies(root.Statement, pending);
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

    private static ImmutableArray<ProductionProject> LoadProductionProjects(
        IReadOnlyList<(string RelativePath, string FullPath)> repositoryFiles) => repositoryFiles
        .Where(static file => file.RelativePath.StartsWith("tools/", StringComparison.Ordinal)
            && !file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)
            && file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
        .Select(static file => ProductionProject.Load(file.RelativePath, file.FullPath))
        .OrderBy(static project => project.RelativePath, StringComparer.Ordinal)
        .ToImmutableArray();

    private sealed record ProductionProject(
        string RelativePath,
        string DirectoryPrefix,
        bool DefaultCompileItems,
        bool IsExecutable,
        ImmutableArray<System.Text.RegularExpressions.Regex> ExplicitCompileIncludes)
    {
        internal static ProductionProject Load(string relativePath, string fullPath)
        {
            var document = XDocument.Load(fullPath, LoadOptions.None);
            var directoryPrefix = relativePath[..(relativePath.LastIndexOf('/') + 1)];
            var defaultCompileItems = !document.Descendants()
                .Where(static element => element.Name.LocalName == "EnableDefaultCompileItems")
                .Select(static element => element.Value.Trim())
                .Any(static value => string.Equals(value, "false", StringComparison.OrdinalIgnoreCase));
            var isExecutable = document.Descendants()
                .Where(static element => element.Name.LocalName == "OutputType")
                .Select(static element => element.Value.Trim())
                .Any(static value => value is "Exe" or "WinExe");
            var explicitCompileIncludes = document.Descendants()
                .Where(static element => element.Name.LocalName == "Compile")
                .Select(static element => (string?)element.Attribute("Include"))
                .Where(static include => !string.IsNullOrWhiteSpace(include))
                .Select(include => GlobRegex(NormalizePattern(directoryPrefix, include!)))
                .ToImmutableArray();
            return new ProductionProject(
                relativePath,
                directoryPrefix,
                defaultCompileItems,
                isExecutable,
                explicitCompileIncludes);
        }

        internal bool Includes(string path) =>
            (DefaultCompileItems && path.StartsWith(DirectoryPrefix, StringComparison.Ordinal))
            || ExplicitCompileIncludes.Any(pattern => pattern.IsMatch(path));

        private static string NormalizePattern(string directoryPrefix, string include)
        {
            var segments = new List<string>();
            foreach (var segment in (directoryPrefix + include.Replace('\\', '/'))
                .Split('/', StringSplitOptions.RemoveEmptyEntries))
            {
                if (segment == ".") continue;
                if (segment == "..")
                {
                    if (segments.Count == 0)
                        throw new InvalidDataException($"compile include escapes repository root: {include}");
                    segments.RemoveAt(segments.Count - 1);
                    continue;
                }
                segments.Add(segment);
            }
            return string.Join('/', segments);
        }

        private static System.Text.RegularExpressions.Regex GlobRegex(string pattern)
        {
            var expression = new System.Text.StringBuilder("^");
            for (var index = 0; index < pattern.Length; index++)
            {
                if (pattern[index] == '*' && index + 1 < pattern.Length && pattern[index + 1] == '*')
                {
                    index++;
                    if (index + 1 < pattern.Length && pattern[index + 1] == '/')
                    {
                        index++;
                        expression.Append("(?:.*/)?");
                    }
                    else
                    {
                        expression.Append(".*");
                    }
                }
                else if (pattern[index] == '*')
                {
                    expression.Append("[^/]*");
                }
                else if (pattern[index] == '?')
                {
                    expression.Append("[^/]");
                }
                else
                {
                    expression.Append(System.Text.RegularExpressions.Regex.Escape(pattern[index].ToString()));
                }
            }
            expression.Append('$');
            return new System.Text.RegularExpressions.Regex(
                expression.ToString(),
                System.Text.RegularExpressions.RegexOptions.CultureInvariant);
        }
    }

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
