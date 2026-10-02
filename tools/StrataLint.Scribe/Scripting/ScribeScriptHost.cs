using System.Collections.Concurrent;
using System.Collections.Immutable;
using System.Globalization;
using System.Reflection;
using System.Runtime.Loader;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Text;

namespace StrataLint.Scribe;

public enum ScribeScriptFailureCode
{
    InvalidPath,
    SharedSourceArgument,
    SharedSourceMissing,
    SharedSourceOutsideBlueprint,
    SharedSourceCycle,
    Compilation,
    BannedSymbol,
    DisallowedSymbol,
    DefinitionMissing,
    MultipleDefinitions,
    GidPathMismatch,
    CreateFailed,
    HostConfiguration,
    SourceRead,
    TypeLoad,
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
    public ImmutableArray<ScribeProjectionRead> ReadSet { get; init; } = [];
    public bool IsSuccess => Definition is not null && Failure is null;
}

/// <summary>
/// 宿主执行定义，并对被执行的代码施加禁用符号规则。
/// 定义的编译准入（含 SDK 与代码风格分析器）不由宿主承担。
/// </summary>
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
        => ExecutePrepared(repositoryRoot, relativePath, references, analyzers, ScriptParseOptions,
            allowlistPath: null, entryTypeOverride: null);

    internal static ScribeScriptResult ExecuteWithDefineConstants(string repositoryRoot, string relativePath,
        string? constants) => ExecutePrepared(repositoryRoot, relativePath, ReferenceAssemblies(), AnalyzerReferences(),
            ReadScriptParseOptions(constants), allowlistPath: null, entryTypeOverride: null);

    internal static ScribeScriptResult ExecuteWithAllowlistPath(
        string repositoryRoot, string relativePath, string allowlistPath) => ExecutePrepared(
            repositoryRoot, relativePath, ReferenceAssemblies(), AnalyzerReferences(), ScriptParseOptions,
            allowlistPath, entryTypeOverride: null);

    internal static ScribeScriptResult ExecuteWithEntryType(
        string repositoryRoot, string relativePath, string entryType) => ExecutePrepared(
            repositoryRoot, relativePath, ReferenceAssemblies(), AnalyzerReferences(), ScriptParseOptions,
            allowlistPath: null, entryType);

    private static ScribeScriptResult ExecutePrepared(string repositoryRoot, string relativePath,
        ImmutableArray<MetadataReference> references, ImmutableArray<DiagnosticAnalyzer> analyzers,
        CSharpParseOptions? parseOptions, string? allowlistPath, string? entryTypeOverride)
    {
        var normalized = NormalizePath(relativePath);
        if (normalized is null)
        {
            return FailureResult(relativePath, ScribeScriptFailureCode.InvalidPath,
                "the definition path must be a normalized relative Blueprint/**/*.scribe.cs path");
        }

        var root = Path.GetFullPath(repositoryRoot);
        if (parseOptions is null)
            return FailureResult(normalized, ScribeScriptFailureCode.HostConfiguration,
                "Documents DefineConstants metadata is unavailable or invalid");
        try
        {
            var sourceGraph = ReadSourceGraph(root, normalized, parseOptions);
            if (sourceGraph.Failure is not null)
            {
                return new(normalized, null, sourceGraph.Failure);
            }
    
            var compilation = Compile(root, normalized, sourceGraph.Sources!.Value, references, analyzers,
                parseOptions, allowlistPath);
            if (compilation.Failure is not null)
            {
                return new(normalized, null, compilation.Failure);
            }
    
            var loadContext = new ScriptLoadContext();
            try
            {
                using var image = compilation.Image!;
                Type type;
                try
                {
                    var assembly = loadContext.LoadFromStream(image);
                    type = assembly.GetType(entryTypeOverride ?? compilation.EntryType!, throwOnError: true)!;
                }
                catch (Exception exception) when (exception is TypeLoadException or FileLoadException
                    or FileNotFoundException or BadImageFormatException)
                {
                    return FailureResult(normalized, ScribeScriptFailureCode.TypeLoad, FirstMessage(exception));
                }
                DocumentDefinition definition;
                var reads = new Dictionary<string, string>(StringComparer.Ordinal);
                ImmutableArray<ScribeProjectionRead> ReadSet() => reads.OrderBy(item => item.Key, StringComparer.Ordinal)
                    .Select(item => new ScribeProjectionRead(item.Key, item.Value)).ToImmutableArray();
                var culture = CultureInfo.CurrentCulture;
                var uiCulture = CultureInfo.CurrentUICulture;
                try
                {
                    CultureInfo.CurrentCulture = CultureInfo.InvariantCulture;
                    CultureInfo.CurrentUICulture = CultureInfo.InvariantCulture;
                    definition = StatementProjectionFixtureLoader.WithRepositoryRoot(root, () =>
                    {
                        var instance = Activator.CreateInstance(type, nonPublic: true)
                            as IScribeDocumentDefinition
                            ?? throw new InvalidOperationException("definition needs a parameterless constructor");
                        return instance.Create();
                    }, reads)
                        ?? throw new InvalidOperationException("definition returned null");
                }
                catch (Exception exception) when (exception is not OutOfMemoryException)
                {
                    return FailureResult(normalized, ScribeScriptFailureCode.CreateFailed, FirstMessage(exception)) with { ReadSet = ReadSet() };
                }
                finally
                {
                    CultureInfo.CurrentCulture = culture;
                    CultureInfo.CurrentUICulture = uiCulture;
                }
                try
                {
                    DocumentDefinitions.ValidateBijection(definition);
                    if (!string.Equals(definition.SourcePath, normalized, StringComparison.Ordinal))
                        throw new InvalidOperationException($"definition source must equal {normalized}, not {definition.SourcePath}");
                }
                catch (InvalidOperationException exception)
                {
                    return FailureResult(normalized, ScribeScriptFailureCode.GidPathMismatch, exception.Message) with { ReadSet = ReadSet() };
                }
                return new(normalized, definition, null) { ReadSet = ReadSet() };
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
        Parallel.ForEach(paths,
            path => results.Add(ExecuteCore(repositoryRoot, path, references, analyzers)));
        return results.OrderBy(result => result.RelativePath, StringComparer.Ordinal).ToImmutableArray();
    }

    internal static (ImmutableArray<string>? Sources, ScribeScriptFailure? Failure) ReadSourceGraph(
        string root,
        string entry,
        CSharpParseOptions? parseOptions = null)
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
            var tree = CSharpSyntaxTree.ParseText(text, parseOptions ?? ScriptParseOptions, path: path);
            foreach (var declaration in tree.GetRoot().DescendantNodes().OfType<TypeDeclarationSyntax>())
            {
                foreach (var attribute in declaration.AttributeLists.SelectMany(list => list.Attributes))
                {
                    if (!IsSharedSourceAttribute(attribute.Name))
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

    private static bool IsSharedSourceAttribute(NameSyntax name)
    {
        var identifier = name switch
        {
            IdentifierNameSyntax simple => simple,
            QualifiedNameSyntax
            {
                Right: IdentifierNameSyntax member,
                Left: QualifiedNameSyntax
                {
                    Right: IdentifierNameSyntax { Identifier.ValueText: "Scribe" },
                    Left: var prefix,
                },
            } when prefix is IdentifierNameSyntax { Identifier.ValueText: "StrataLint" }
                or AliasQualifiedNameSyntax
                {
                    Alias.Identifier.ValueText: "global",
                    Name: IdentifierNameSyntax { Identifier.ValueText: "StrataLint" },
                } => member,
            _ => null,
        };
        return identifier?.Identifier.ValueText is "ScribeSharedSource" or nameof(ScribeSharedSourceAttribute);
    }

    private static (MemoryStream? Image, string? EntryType, ScribeScriptFailure? Failure) Compile(
        string root,
        string entry,
        ImmutableArray<string> sources,
        ImmutableArray<MetadataReference> references,
        ImmutableArray<DiagnosticAnalyzer> analyzers,
        CSharpParseOptions parseOptions,
        string? allowlistPath)
    {
        var trees = sources.Select(path => CSharpSyntaxTree.ParseText(
            File.ReadAllText(Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar))),
            parseOptions,
            path: path)).Append(CSharpSyntaxTree.ParseText(
                "global using System; global using System.Collections.Generic; global using System.IO; "
                + "global using System.Linq; global using System.Net.Http; global using System.Threading; "
                + "global using System.Threading.Tasks;", parseOptions, path: "ScriptGlobalUsings.cs")).ToImmutableArray();
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
        foreach (var tree in trees.Where(tree => sources.Contains(tree.FilePath, StringComparer.Ordinal)))
        {
            foreach (var node in tree.GetRoot().DescendantNodesAndSelf())
            {
                if (node is UnsafeStatementSyntax or PointerTypeSyntax or FunctionPointerTypeSyntax
                    || node is MethodDeclarationSyntax method && method.Modifiers.Any(SyntaxKind.ExternKeyword))
                    return (null, null, MakeFailure(tree.FilePath, ScribeScriptFailureCode.DisallowedSymbol,
                        $"{tree.FilePath}:{node.GetLocation().GetLineSpan().StartLinePosition.Line + 1}: disallowed unsafe, pointer, function-pointer, or extern syntax"));
            }
        }
        var compileError = compilation.GetDiagnostics().FirstOrDefault(d => d.Severity == DiagnosticSeverity.Error);
        if (compileError is not null)
            return (null, null, MakeFailure(entry, ScribeScriptFailureCode.Compilation, compileError.ToString()));

        var contract = compilation.GetTypeByMetadataName(typeof(IScribeDocumentDefinition).FullName!)!;
        var entryTypes = compilation.GetSymbolsWithName(static _ => true, SymbolFilter.Type)
            .OfType<INamedTypeSymbol>()
            .Where(symbol => !symbol.IsAbstract
                && symbol.AllInterfaces.Contains(contract, SymbolEqualityComparer.Default)
                && symbol.Locations.Any(location => string.Equals(location.SourceTree?.FilePath, entry, StringComparison.Ordinal)))
            .Select(MetadataName).Distinct(StringComparer.Ordinal).ToArray();
        if (entryTypes.Length != 1)
            return (null, null, MakeFailure(entry, entryTypes.Length == 0
                ? ScribeScriptFailureCode.DefinitionMissing : ScribeScriptFailureCode.MultipleDefinitions,
                $"entry source contains {entryTypes.Length} concrete document definitions"));
        var allowlist = ScribeScriptAllowlist.Read(compilation, entry, allowlistPath);
        if (allowlist.Failure is not null)
            return (null, null, allowlist.Failure);
        var symbolFailure = ScribeScriptAdmission.Validate(compilation, sources, allowlist.Table!);
        if (symbolFailure is not null)
            return (null, null, symbolFailure);

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
        : NamespaceMetadataName(symbol.ContainingNamespace) + symbol.MetadataName;

    private static string NamespaceMetadataName(INamespaceSymbol symbol) => symbol.IsGlobalNamespace
        ? string.Empty
        : NamespaceMetadataName(symbol.ContainingNamespace) + symbol.MetadataName + ".";

    private sealed class RuleText(string path) : AdditionalText
    {
        public override string Path => path;
        public override SourceText GetText(CancellationToken cancellationToken = default) => SourceText.From(File.ReadAllText(path));
    }

    private static readonly CSharpParseOptions? ScriptParseOptions = ReadScriptParseOptions(
        typeof(ScribeScriptHost).Assembly.GetCustomAttributes<AssemblyMetadataAttribute>()
            .FirstOrDefault(attribute => attribute.Key == "ScribeScriptDefineConstants")?.Value);

    private static CSharpParseOptions? ReadScriptParseOptions(string? constants)
    {
        if (string.IsNullOrWhiteSpace(constants)) return null;
        var symbols = constants.Split(';', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .Distinct(StringComparer.Ordinal).ToArray();
        return symbols.Length == 0 || symbols.Any(symbol => !SyntaxFacts.IsValidIdentifier(symbol))
            ? null
            : new CSharpParseOptions(LanguageVersion.CSharp14, DocumentationMode.Parse,
                SourceCodeKind.Regular, symbols);
    }

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
