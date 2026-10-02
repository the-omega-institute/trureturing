using System.Collections.Concurrent;
using System.Collections.Immutable;
using System.Reflection;
using System.Runtime.Loader;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Text;

namespace StrataLint.Scribe.Scripting;

public enum ScribeScriptFailureCode
{
    InvalidPath,
    SharedSourceArgument,
    SharedSourceMissing,
    SharedSourceOutsideBlueprint,
    SharedSourceCycle,
    Compilation,
    BannedSymbol,
    DefinitionMissing,
    MultipleDefinitions,
    GidPathMismatch,
    CreateFailed,
    HostConfiguration,
    SourceRead,
}

public sealed record ScribeScriptFailure(
    ScribeScriptFailureCode Code,
    string RelativePath,
    string Message)
{
    public override string ToString() => $"{Code}: {RelativePath}: {Message}";
}

public sealed record ScribeScriptResult(
    string RelativePath,
    DocumentDefinition? Definition,
    ScribeScriptFailure? Failure)
{
    public bool IsSuccess => Definition is not null && Failure is null;
}

public static class ScribeScriptHost
{
    private const string BlueprintPrefix = "Blueprint/";
    private const string SourceSuffix = ".scribe.cs";

    public static ScribeScriptResult Execute(string repositoryRoot, string relativePath)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentException.ThrowIfNullOrWhiteSpace(relativePath);
        return ExecuteCore(repositoryRoot, relativePath, ReferenceAssemblies(), AnalyzerReferences());
    }

    private static ScribeScriptResult ExecuteCore(string repositoryRoot, string relativePath,
        ImmutableArray<MetadataReference> references, ImmutableArray<DiagnosticAnalyzer> analyzers)
    {
        var normalized = NormalizePath(relativePath);
        if (normalized is null)
        {
            return FailureResult(relativePath, ScribeScriptFailureCode.InvalidPath,
                "the definition path must be a normalized relative Blueprint/**/*.scribe.cs path");
        }

        var root = Path.GetFullPath(repositoryRoot);
        try
        {
            var sourceGraph = ReadSourceGraph(root, normalized);
            if (sourceGraph.Failure is not null)
            {
                return new(normalized, null, sourceGraph.Failure);
            }
    
            var compilation = Compile(root, normalized, sourceGraph.Sources!.Value, references, analyzers);
            if (compilation.Failure is not null)
            {
                return new(normalized, null, compilation.Failure);
            }
    
            var loadContext = new ScriptLoadContext();
            try
            {
                using var image = compilation.Image!;
                var assembly = loadContext.LoadFromStream(image);
                var type = assembly.GetType(compilation.EntryType!, throwOnError: true)!;
                DocumentDefinition definition;
                try
                {
                    var instance = Activator.CreateInstance(type, nonPublic: true)
                        as IScribeDocumentDefinition
                        ?? throw new InvalidOperationException("definition needs a parameterless constructor");
                    definition = StatementProjectionFixtureLoader.WithRepositoryRoot(root, instance.Create)
                        ?? throw new InvalidOperationException("definition returned null");
                }
                catch (Exception exception) when (exception is not OutOfMemoryException)
                {
                    return FailureResult(normalized, ScribeScriptFailureCode.CreateFailed, FirstMessage(exception));
                }
                try
                {
                    DocumentDefinitions.ValidateBijection(definition);
                    if (!string.Equals(definition.SourcePath, normalized, StringComparison.Ordinal))
                        throw new InvalidOperationException($"definition source must equal {normalized}, not {definition.SourcePath}");
                }
                catch (InvalidOperationException exception)
                {
                    return FailureResult(normalized, ScribeScriptFailureCode.GidPathMismatch, exception.Message);
                }
                return new(normalized, definition, null);
            }
            finally
            {
                loadContext.Unload();
            }
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
        {
            return FailureResult(normalized, ScribeScriptFailureCode.SourceRead, exception.Message);
        }
    }

    public static ImmutableArray<ScribeScriptResult> ExecuteBatch(
        string repositoryRoot,
        IEnumerable<string> relativePaths)
    {
        ArgumentNullException.ThrowIfNull(relativePaths);
        var paths = relativePaths.ToArray();
        var results = new ConcurrentBag<ScribeScriptResult>();
        var references = ReferenceAssemblies();
        var analyzers = AnalyzerReferences();
        Parallel.ForEach(paths, new ParallelOptions { MaxDegreeOfParallelism = Math.Min(Environment.ProcessorCount, 16) },
            path => results.Add(ExecuteCore(repositoryRoot, path, references, analyzers)));
        return results.OrderBy(result => result.RelativePath, StringComparer.Ordinal).ToImmutableArray();
    }

    private static (ImmutableArray<string>? Sources, ScribeScriptFailure? Failure) ReadSourceGraph(
        string root,
        string entry)
    {
        var sources = new List<string>();
        var visiting = new HashSet<string>(StringComparer.Ordinal);
        var visited = new HashSet<string>(StringComparer.Ordinal);
        ScribeScriptFailure? failure = null;

        void Visit(string path)
        {
            if (failure is not null || visited.Contains(path)) return;
            if (!visiting.Add(path))
            {
                failure = MakeFailure(path, ScribeScriptFailureCode.SharedSourceCycle,
                    "shared source declaration contains a cycle");
                return;
            }

            var full = Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));
            if (!File.Exists(full))
            {
                failure = MakeFailure(path, ScribeScriptFailureCode.SharedSourceMissing,
                    "declared shared source does not exist");
                return;
            }

            var text = File.ReadAllText(full);
            var tree = CSharpSyntaxTree.ParseText(text, ScriptParseOptions, path: path);
            foreach (var declaration in tree.GetRoot().DescendantNodes().OfType<ClassDeclarationSyntax>())
            {
                foreach (var attribute in declaration.AttributeLists.SelectMany(list => list.Attributes))
                {
                    var name = attribute.Name.ToString();
                    var attributeName = typeof(ScribeSharedSourceAttribute).Name;
                    var shortAttributeName = attributeName[..^"Attribute".Length];
                    if (!name.EndsWith(attributeName, StringComparison.Ordinal)
                        && !name.EndsWith(shortAttributeName, StringComparison.Ordinal))
                    {
                        continue;
                    }

                    var arguments = attribute.ArgumentList?.Arguments;
                    var argument = arguments is { Count: 1 } ? arguments.Value[0] : null;
                    if (argument?.Expression is not LiteralExpressionSyntax literal
                        || !literal.IsKind(SyntaxKind.StringLiteralExpression))
                    {
                        failure = MakeFailure(path, ScribeScriptFailureCode.SharedSourceArgument,
                            "shared source attribute requires one string literal argument");
                        return;
                    }

                    var declared = NormalizePath(literal.Token.ValueText);
                    if (declared is null || !declared.StartsWith(BlueprintPrefix, StringComparison.Ordinal)
                        || !declared.EndsWith(SourceSuffix, StringComparison.Ordinal))
                    {
                        failure = MakeFailure(path, ScribeScriptFailureCode.SharedSourceOutsideBlueprint,
                            $"declared shared source is outside Blueprint/**/*.scribe.cs: {literal.Token.ValueText}");
                        return;
                    }

                    Visit(declared);
                    if (failure is not null) return;
                }
            }

            visiting.Remove(path);
            visited.Add(path);
            sources.Add(path);
        }

        Visit(entry);
        return failure is null
            ? (sources.ToImmutableArray(), null)
            : (null, failure);
    }

    private static (MemoryStream? Image, string? EntryType, ScribeScriptFailure? Failure) Compile(
        string root,
        string entry,
        ImmutableArray<string> sources,
        ImmutableArray<MetadataReference> references,
        ImmutableArray<DiagnosticAnalyzer> analyzers)
    {
        var trees = sources.Select(path => CSharpSyntaxTree.ParseText(
            File.ReadAllText(Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar))),
            ScriptParseOptions,
            path: path)).Append(CSharpSyntaxTree.ParseText(
                "global using System; global using System.Collections.Generic; global using System.IO; "
                + "global using System.Linq; global using System.Net.Http; global using System.Threading; "
                + "global using System.Threading.Tasks;", ScriptParseOptions, path: "ScriptGlobalUsings.cs")).ToImmutableArray();
        var compilation = CSharpCompilation.Create(
            "StrataLint.Scribe.Documents",
            trees,
            references,
            ScriptCompilationOptions);

        if (analyzers.IsEmpty)
            return (null, null, MakeFailure(entry, ScribeScriptFailureCode.HostConfiguration, "banned API analyzer is unavailable"));
        var directory = Path.Combine(AppContext.BaseDirectory, "Scripting");
        var additionalFiles = new[] { "BannedSymbols.txt", "BannedSymbols.Determinism.txt", "BannedSymbols.Guid.txt" }
            .Select(name => (AdditionalText)new RuleText(Path.Combine(directory, name))).ToImmutableArray();
        var analyzerOptions = new AnalyzerOptions(additionalFiles);
        var diagnostics = compilation.GetDiagnostics().AddRange(
            compilation.WithAnalyzers(analyzers, analyzerOptions).GetAnalyzerDiagnosticsAsync().GetAwaiter().GetResult());
        var first = diagnostics
            .Where(diagnostic => diagnostic.Severity is DiagnosticSeverity.Error or DiagnosticSeverity.Warning)
            .OrderBy(diagnostic => diagnostic.Location.GetLineSpan().Path, StringComparer.Ordinal)
            .ThenBy(diagnostic => diagnostic.Location.SourceSpan.Start)
            .ThenBy(diagnostic => diagnostic.Id, StringComparer.Ordinal)
            .FirstOrDefault();
        if (first is not null)
        {
            var code = first.Id is "RS0030" or "RS0031" or "RS0035"
                ? ScribeScriptFailureCode.BannedSymbol
                : ScribeScriptFailureCode.Compilation;
            return (null, null, MakeFailure(entry, code, first.ToString()));
        }

        var contract = compilation.GetTypeByMetadataName(typeof(IScribeDocumentDefinition).FullName!)!;
        var entryTree = trees.Single(tree => tree.FilePath == entry);
        var model = compilation.GetSemanticModel(entryTree);
        var entryTypes = entryTree.GetRoot().DescendantNodes().OfType<ClassDeclarationSyntax>()
            .Select(declaration => model.GetDeclaredSymbol(declaration))
            .OfType<INamedTypeSymbol>()
            .Where(symbol => !symbol.IsAbstract && symbol.AllInterfaces.Contains(contract, SymbolEqualityComparer.Default))
            .Select(MetadataName).Distinct(StringComparer.Ordinal).ToArray();
        if (entryTypes.Length != 1)
            return (null, null, MakeFailure(entry, entryTypes.Length == 0
                ? ScribeScriptFailureCode.DefinitionMissing : ScribeScriptFailureCode.MultipleDefinitions,
                $"entry source contains {entryTypes.Length} concrete document definitions"));
        var image = new MemoryStream();
        var emit = compilation.Emit(image);
        if (!emit.Success)
        {
            var diagnostic = emit.Diagnostics.FirstOrDefault(d => d.Severity == DiagnosticSeverity.Error)
                ?? emit.Diagnostics.First();
            image.Dispose();
            return (null, null, MakeFailure(entry, ScribeScriptFailureCode.Compilation, diagnostic.ToString()));
        }

        image.Position = 0;
        return (image, entryTypes[0], null);
    }

    private static ImmutableArray<MetadataReference> ReferenceAssemblies()
    {
        var paths = new HashSet<string>(StringComparer.Ordinal);
        var runtimeDirectory = Path.GetDirectoryName(typeof(object).Assembly.Location)!;
        var tpa = AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") as string;
        foreach (var path in (tpa ?? string.Empty).Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries))
            if (Path.GetDirectoryName(path) == runtimeDirectory) paths.Add(path);
        var seen = new HashSet<string>(StringComparer.Ordinal);
        void Include(Assembly assembly)
        {
            if (!seen.Add(assembly.FullName!)) return;
            paths.Add(assembly.Location);
            foreach (var dependency in assembly.GetReferencedAssemblies()) Include(Assembly.Load(dependency));
        }
        Include(typeof(DocumentDefinition).Assembly);
        return paths.Order(StringComparer.Ordinal)
            .Select(static path => (MetadataReference)MetadataReference.CreateFromFile(path)).ToImmutableArray();
    }

    private static ImmutableArray<DiagnosticAnalyzer> AnalyzerReferences()
    {
        var analyzerPath = Path.Combine(AppContext.BaseDirectory, "Scripting", "Microsoft.CodeAnalysis.CSharp.BannedApiAnalyzers.dll");
        if (!File.Exists(analyzerPath)) return [];
        var reference = new AnalyzerFileReference(analyzerPath, new ScriptAnalyzerAssemblyLoader());
        return reference.GetAnalyzers(LanguageNames.CSharp).ToImmutableArray();
    }

    private static string MetadataName(INamedTypeSymbol symbol) => symbol.ContainingType is { } parent
        ? MetadataName(parent) + "+" + symbol.MetadataName
        : (symbol.ContainingNamespace.IsGlobalNamespace ? string.Empty : symbol.ContainingNamespace + ".") + symbol.MetadataName;

    private sealed class RuleText(string path) : AdditionalText
    {
        public override string Path => path;
        public override SourceText GetText(CancellationToken cancellationToken = default) => SourceText.From(File.ReadAllText(path));
    }

    private static readonly CSharpParseOptions ScriptParseOptions = new(
        LanguageVersion.CSharp14,
        DocumentationMode.Parse,
        SourceCodeKind.Regular);

    private static readonly CSharpCompilationOptions ScriptCompilationOptions = new(
        OutputKind.DynamicallyLinkedLibrary,
        optimizationLevel: OptimizationLevel.Release,
        nullableContextOptions: NullableContextOptions.Enable,
        warningLevel: 999,
        generalDiagnosticOption: ReportDiagnostic.Error,
        deterministic: true);

    private static string? NormalizePath(string path)
    {
        if (string.IsNullOrWhiteSpace(path) || Path.IsPathRooted(path)) return null;
        var normalized = path.Replace('\\', '/');
        if (normalized.Split('/').Any(segment => segment is "" or "." or "..")) return null;
        return normalized.StartsWith(BlueprintPrefix, StringComparison.Ordinal)
            && normalized.EndsWith(SourceSuffix, StringComparison.Ordinal)
            ? normalized
            : null;
    }

    private static ScribeScriptFailure MakeFailure(string path, ScribeScriptFailureCode code, string message) =>
        new(code, path, message);

    private static ScribeScriptResult FailureResult(string path, ScribeScriptFailureCode code, string message) =>
        new(NormalizePath(path) ?? path.Replace('\\', '/'), null, MakeFailure(path, code, message));

    private static string FirstMessage(Exception exception) =>
        exception.InnerException is null ? exception.Message : FirstMessage(exception.InnerException);

    private sealed class ScriptLoadContext : AssemblyLoadContext
    {
        internal ScriptLoadContext() : base(isCollectible: true) { }

        protected override Assembly? Load(AssemblyName assemblyName) =>
            Default.Assemblies.FirstOrDefault(assembly => AssemblyName.ReferenceMatchesDefinition(
                assembly.GetName(), assemblyName)) ?? Default.LoadFromAssemblyName(assemblyName);
    }

    private sealed class ScriptAnalyzerAssemblyLoader : IAnalyzerAssemblyLoader
    {
        public void AddDependencyLocation(string fullPath) { }

        public Assembly LoadFromPath(string fullPath) => Assembly.LoadFrom(fullPath);
    }
}
