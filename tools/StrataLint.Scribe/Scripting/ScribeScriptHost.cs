using System.Collections.Concurrent;
using System.Collections.Immutable;
using System.Globalization;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using System.Runtime.Loader;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Text;

namespace StrataLint.Scribe;

public enum ScribeScriptFailureCode
{
    InvalidPath,
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
    private const string LoadDiagnosticPrefix = "STRATALINT_SCRIBE_LOAD_DIAGNOSTIC";
    private const int LoadDiagnosticChunkBytes = 3072;
    private const int LoadDiagnosticMaxImageBytes = 512 * 1024;
    private const int LoadDiagnosticMaxExceptionChars = 128 * 1024;
    private static long loadDiagnosticSequence;

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
        string repositoryRoot, string relativePath, string allowlistPath, TextWriter? diagnosticWriter = null) => ExecutePrepared(
            repositoryRoot, relativePath, ReferenceAssemblies(), AnalyzerReferences(), ScriptParseOptions,
            allowlistPath, entryTypeOverride: null, diagnosticWriter);

    internal static ScribeScriptResult ExecuteWithEntryType(
        string repositoryRoot, string relativePath, string entryType, TextWriter? diagnosticWriter = null) => ExecutePrepared(
            repositoryRoot, relativePath, ReferenceAssemblies(), AnalyzerReferences(), ScriptParseOptions,
            allowlistPath: null, entryType, diagnosticWriter);

    private static ScribeScriptResult ExecutePrepared(string repositoryRoot, string relativePath,
        ImmutableArray<MetadataReference> references, ImmutableArray<DiagnosticAnalyzer> analyzers,
        CSharpParseOptions? parseOptions, string? allowlistPath, string? entryTypeOverride,
        TextWriter? diagnosticWriter = null)
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
                "Scribe DefineConstants metadata is unavailable or invalid");
        try
        {
            var compilation = Compile(root, normalized, [normalized], references, analyzers,
                parseOptions, allowlistPath);
            if (compilation.Failure is not null)
            {
                return new(normalized, null, compilation.Failure);
            }
    
            var loadContext = new ScriptLoadContext();
            try
            {
                using var image = compilation.Image!;
                Assembly? assembly = null;
                Type type;
                try
                {
                    assembly = loadContext.LoadFromStream(image);
                    type = assembly.GetType(entryTypeOverride ?? compilation.EntryType!, throwOnError: true)!;
                }
                catch (Exception exception) when (exception is TypeLoadException or FileLoadException
                    or FileNotFoundException or BadImageFormatException)
                {
                    EmitLoadDiagnostic(normalized, entryTypeOverride ?? compilation.EntryType!, references,
                        image, assembly, loadContext, exception, diagnosticWriter);
                    return FailureResult(normalized, ScribeScriptFailureCode.TypeLoad, FirstMessage(exception));
                }
                DocumentDefinition definition;
                var culture = CultureInfo.CurrentCulture;
                var uiCulture = CultureInfo.CurrentUICulture;
                try
                {
                    CultureInfo.CurrentCulture = CultureInfo.InvariantCulture;
                    CultureInfo.CurrentUICulture = CultureInfo.InvariantCulture;
                    definition = StatementProjectionFixtureLoader.WithScriptRepositoryRoot(root, () =>
                    {
                        var instance = Activator.CreateInstance(type, nonPublic: true)
                            as IScribeDocumentDefinition
                            ?? throw new InvalidOperationException("definition needs a parameterless constructor");
                        return instance.Create();
                    })
                        ?? throw new InvalidOperationException("definition returned null");
                }
                catch (Exception exception) when (exception is not OutOfMemoryException)
                {
                    return FailureResult(normalized, ScribeScriptFailureCode.CreateFailed, FirstMessage(exception));
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
        Parallel.ForEach(paths,
            path => results.Add(ExecuteCore(repositoryRoot, path, references, analyzers)));
        return results.OrderBy(result => result.RelativePath, StringComparer.Ordinal).ToImmutableArray();
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
        var compilation = CreateSourceCompilation(root, sources, references, parseOptions);
        var trees = compilation.SyntaxTrees;

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

    private static CSharpCompilation CreateSourceCompilation(string root, ImmutableArray<string> sources,
        ImmutableArray<MetadataReference> references, CSharpParseOptions parseOptions)
    {
        var trees = sources.Select(path => CSharpSyntaxTree.ParseText(
            File.ReadAllText(Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar))),
            parseOptions,
            path: path)).Append(CSharpSyntaxTree.ParseText(
                "global using System; global using System.Collections.Generic; global using System.IO; "
                + "global using System.Linq; global using System.Net.Http; global using System.Threading; "
                + "global using System.Threading.Tasks;", parseOptions, path: "ScriptGlobalUsings.cs")).ToImmutableArray();
        return CSharpCompilation.Create(
            "StrataLint.Scribe.Script",
            trees,
            references,
            ScriptCompilationOptions);
    }

    internal static ImmutableArray<MetadataReference> ReferenceAssemblies()
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

    private static void EmitLoadDiagnostic(
        string relativePath,
        string entryType,
        ImmutableArray<MetadataReference> references,
        MemoryStream image,
        Assembly? assembly,
        AssemblyLoadContext loadContext,
        Exception exception,
        TextWriter? diagnosticWriter)
    {
        var writer = diagnosticWriter ?? Console.Error;
        var capture = string.Empty;
        void WriteLine(string kind, string payload) =>
            writer.WriteLine($"{LoadDiagnosticPrefix}_{kind} capture={capture} {payload}");
        void WriteField(string key, string value) => WriteLine("FIELD", $"{key}={Sanitize(value)}");
        try
        {
            capture = Environment.ProcessId.ToString(CultureInfo.InvariantCulture) + "-"
                + Interlocked.Increment(ref loadDiagnosticSequence).ToString(CultureInfo.InvariantCulture);
            var bytes = image.ToArray();
            var complete = bytes.Length <= LoadDiagnosticMaxImageBytes;
            var digest = Convert.ToHexStringLower(SHA256.HashData(bytes));
            var imageMetadata = ReadPeMetadata(bytes);
            var exceptionText = exception.ToString();
            var exceptionComplete = exceptionText.Length <= LoadDiagnosticMaxExceptionChars;
            var exceptionPayload = exceptionComplete
                ? exceptionText
                : exceptionText[..LoadDiagnosticMaxExceptionChars];
            WriteLine("BEGIN", "version=2");
            WriteField("source_utf8_base64", EncodeUtf8(relativePath));
            WriteField("entry_utf8_base64", EncodeUtf8(entryType));
            WriteField("failure_code", ScribeScriptFailureCode.TypeLoad.ToString());
            WriteField("failure_exception_utf8_base64", EncodeUtf8(exceptionPayload));
            WriteField("failure_exception_complete", exceptionComplete ? "true" : "false");
            WriteField("image_length", bytes.Length.ToString(CultureInfo.InvariantCulture));
            WriteField("image_sha256", digest);
            WriteField("image_mvid", imageMetadata);
            WriteField("payload_complete", complete ? "true" : "false");
            if (!complete)
                WriteField("payload_incomplete_reason", $"image exceeds {LoadDiagnosticMaxImageBytes} bytes");

            WriteField("runtime_framework", RuntimeInformation.FrameworkDescription);
            WriteField("runtime_version", Environment.Version.ToString());
            WriteField("os_description", RuntimeInformation.OSDescription);
            WriteField("os_architecture", RuntimeInformation.OSArchitecture.ToString());
            WriteField("process_architecture", RuntimeInformation.ProcessArchitecture.ToString());
            WriteField("testhost_process", Environment.ProcessPath ?? "unknown");
            WriteField("managed_core_library_path", typeof(object).Assembly.Location);
            WriteField("scribe_host_path", typeof(ScribeScriptHost).Assembly.Location);
            WriteField("roslyn_compiler", typeof(CSharpCompilation).Assembly.FullName ?? "unknown");
            WriteField("roslyn_compiler_path", typeof(CSharpCompilation).Assembly.Location);
            WriteField("sdk_compiler", "in-process Roslyn; no external SDK compiler invoked");
            WriteField("load_context_collectible", loadContext.IsCollectible ? "true" : "false");
            WriteField("load_context_name", loadContext.Name ?? "<null>");
            WriteField("loaded_assembly", assembly?.FullName ?? "<load failed>");
            WriteField("loaded_assembly_mvid", assembly is null ? "<load failed>" : ReadAssemblyMvid(assembly));
            WriteField("loaded_context_name", assembly is null
                ? "<load failed>"
                : AssemblyLoadContext.GetLoadContext(assembly)?.Name ?? "<null>");

            WriteField("reference_count", references.Length.ToString(CultureInfo.InvariantCulture));
            for (var index = 0; index < references.Length; index++)
            {
                var display = references[index].Display ?? "<null>";
                var reference = ReadReferenceMetadata(display);
                WriteField($"reference_{index}_display", display);
                WriteField($"reference_{index}_identity", reference.Identity);
                WriteField($"reference_{index}_mvid", reference.Mvid);
            }

            if (complete)
            {
                for (var offset = 0; offset < bytes.Length; offset += LoadDiagnosticChunkBytes)
                {
                    var length = Math.Min(LoadDiagnosticChunkBytes, bytes.Length - offset);
                    var chunk = Convert.ToBase64String(bytes, offset, length);
                    WriteLine("CHUNK",
                        $"index={offset / LoadDiagnosticChunkBytes} offset={offset} length={length} base64={chunk}");
                }
            }

            WriteLine("END",
                $"chunks={(complete ? (bytes.Length + LoadDiagnosticChunkBytes - 1) / LoadDiagnosticChunkBytes : 0)}");
        }
        catch (Exception diagnosticFailure) when (diagnosticFailure is not OutOfMemoryException)
        {
            // A diagnostic must never alter TypeLoad semantics. If the sink itself fails,
            // leave an explicit incomplete marker on the same sink.
            try
            {
                WriteLine("INCOMPLETE", $"reason={Sanitize(diagnosticFailure.Message)}");
            }
            catch (Exception) { }
        }
    }

    private static string EncodeUtf8(string value) => Convert.ToBase64String(Encoding.UTF8.GetBytes(value));

    private static string Sanitize(string value) => value.Replace("\r", "\\r", StringComparison.Ordinal)
        .Replace("\n", "\\n", StringComparison.Ordinal);

    private static string ReadAssemblyMvid(Assembly assembly)
    {
        try { return assembly.ManifestModule.ModuleVersionId.ToString("D"); }
        catch (Exception) { return "<unavailable>"; }
    }

    private static (string Identity, string Mvid) ReadReferenceMetadata(string display)
    {
        if (string.IsNullOrWhiteSpace(display) || !File.Exists(display))
            return ("<unavailable>", "<unavailable>");
        try
        {
            using var stream = File.OpenRead(display);
            using var pe = new PEReader(stream);
            var reader = pe.GetMetadataReader();
            var module = reader.GetModuleDefinition();
            var mvid = reader.GetGuid(module.Mvid).ToString("D");
            var identity = AssemblyName.GetAssemblyName(display).FullName ?? "<unavailable>";
            return (identity, mvid);
        }
        catch (Exception) { return ("<unavailable>", "<unavailable>"); }
    }

    private static string ReadPeMetadata(byte[] bytes)
    {
        try
        {
            using var stream = new MemoryStream(bytes, writable: false);
            using var pe = new PEReader(stream);
            var reader = pe.GetMetadataReader();
            return reader.GetGuid(reader.GetModuleDefinition().Mvid).ToString("D");
        }
        catch (Exception) { return "<unavailable>"; }
    }

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
