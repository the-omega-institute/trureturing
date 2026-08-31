using System.Collections.Immutable;
using System.Xml.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

// A semantic source index for the two remaining retired-ledger assertions. It deliberately
// does not build a transitive executable reachability graph.
internal sealed class ProductionSourceGraph
{
    private const string HistoricalFreezeMatcherName = "HistoricalActiveFreezeMatches";
    private const string ScribeSourceSuffix = ".scribe.cs";

    private readonly CSharpCompilation compilation;
    private readonly IReadOnlyDictionary<SyntaxTree, string> paths;
    private readonly Dictionary<IMethodSymbol, SyntaxNode> declarations;
    private readonly ImmutableArray<string> executableEntryPointDescriptions;

    private ProductionSourceGraph(
        CSharpCompilation compilation,
        IReadOnlyDictionary<SyntaxTree, string> paths,
        Dictionary<IMethodSymbol, SyntaxNode> declarations,
        ImmutableArray<string> executableEntryPointDescriptions)
    {
        this.compilation = compilation;
        this.paths = paths;
        this.declarations = declarations;
        this.executableEntryPointDescriptions = executableEntryPointDescriptions;
    }

    internal static ProductionSourceGraph Create(string repositoryRoot)
    {
        var repositoryFiles = GitIndexRepositoryFiles.Enumerate(repositoryRoot);
        var projects = LoadProductionProjects(repositoryFiles);
        var files = repositoryFiles
            .Where(file => file.RelativePath.EndsWith(".cs", StringComparison.Ordinal)
                && projects.Any(project => project.Includes(file.RelativePath)))
            .Select(file => new SourceFile(
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .ToArray();

        // Parse every ordinary production C# source so escaped identifiers and non-textual
        // formatting cannot hide an Engine definition or invocation. Blueprint/**/*.scribe.cs
        // is a separate assembly/namespace: screen those 2508 files lexically and parse only a
        // file mentioning the target, then let Roslyn distinguish a Scribe method from the
        // Engine symbol. Executable sources are already part of the ordinary set.
        var selectedFiles = files
            .Where(file => !IsScribeSource(file.RelativePath)
                || file.Text.Contains(HistoricalFreezeMatcherName, StringComparison.Ordinal))
            .ToArray();
        var sources = selectedFiles
            .Select(file => (
                file.RelativePath,
                Tree: CSharpSyntaxTree.ParseText(
                    file.Text,
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
        }

        var entryPoints = ImmutableArray.CreateBuilder<string>();
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
                entryPoints.Add($"{project.RelativePath}::{Display(item.Key)}");
            }
            foreach (var item in projectTopLevel)
            {
                entryPoints.Add($"{project.RelativePath}::top-level:{item.RelativePath}");
            }
        }

        return new ProductionSourceGraph(
            compilation,
            paths,
            declarations,
            entryPoints
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .ToImmutableArray());
    }

    internal IReadOnlyList<string> ExecutableEntryPointDescriptions => executableEntryPointDescriptions;

    internal IReadOnlyList<string> MethodDefinitionsNamed(string name) => declarations
        .Where(item => string.Equals(item.Key.Name, name, StringComparison.Ordinal)
            && !IsScribeSource(paths[item.Value.SyntaxTree]))
        .Select(static item => Display(item.Key))
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

    private static IEnumerable<IMethodSymbol> BoundMethods(SemanticModel model, SyntaxNode node) =>
        Symbols(model.GetSymbolInfo(node)).OfType<IMethodSymbol>();

    private static IEnumerable<ISymbol> Symbols(SymbolInfo info)
    {
        if (info.Symbol is not null) yield return info.Symbol;
        foreach (var candidate in info.CandidateSymbols) yield return candidate;
    }

    private static IMethodSymbol Normalize(IMethodSymbol method) =>
        (method.ReducedFrom ?? method).OriginalDefinition;

    private static string Display(ISymbol symbol) =>
        symbol.ToDisplayString(SymbolDisplayFormat.CSharpErrorMessageFormat);

    private static bool IsScribeSource(string path) =>
        path.EndsWith(ScribeSourceSuffix, StringComparison.Ordinal);

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

    private sealed record SourceFile(string RelativePath, string Text);
}
