using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace StrataLint.ArchitectureTests;

internal sealed record ProductionTestOnlyTypeFinding(
    string QualifiedName,
    string TypeName,
    IReadOnlyList<string> DeclarationPaths,
    IReadOnlyList<string> ReferencePaths,
    string? AllowlistReason)
{
    internal bool IsAllowlisted => AllowlistReason is not null;
}

internal static class ProductionTestOnlyTypePolicy
{
    private static readonly string[] ProductionPrefixes =
    [
        "tools/StrataLint.Cli/",
        "tools/StrataLint.Engine/",
        "tools/StrataLint.Scribe/",
    ];

    private static readonly IReadOnlyDictionary<string, string> Allowlist =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            // Validation fixture: the reader verifies writer round trips and strict schema
            // boundaries. Those decoding and information-preservation checks are orthogonal
            // to DagEmitter's double-write check, which establishes determinism only.
            ["Trureturing.Truth.TruthGraphJsonReader"] =
                "round-trip and strict-schema validation is orthogonal to emitter determinism",

            // Declared producer: spec A17 (line 142) records QuestPDF as active and imposes
            // an annual review. The missing production route is not absence of a specified use.
            ["StrataLint.Scribe.QuestPdfWriter"] =
                "spec A17 declares the producer active with an annual review obligation",
        };

    internal static IReadOnlyList<ProductionTestOnlyTypeFinding> InspectRepository(
        string repositoryRoot)
    {
        var sources = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .Select(file => new SourceFile(
                file.RelativePath,
                CSharpSyntaxTree.ParseText(
                    File.ReadAllText(file.FullPath),
                    CSharpParseOptions.Default.WithLanguageVersion(LanguageVersion.Preview),
                    file.RelativePath)))
            .ToArray();

        // The Git-index scan intentionally includes every tracked C# source, not just tools/.
        // In particular Blueprint/**/*.scribe.cs contains the production consumers that keep
        // ScribeNode alive; omitting those 609 references produced a measured false positive.
        var compilation = CSharpCompilation.Create(
            "ProductionTestOnlyTypeAnalysis",
            sources.Select(static source => source.Tree).Append(ImplicitUsingsTree()),
            PlatformReferences(),
            new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));

        var candidates = CollectCandidates(compilation, sources);
        CollectReferences(compilation, sources, candidates);

        return candidates.Values
            // With no non-declaration references, All(test-path) is vacuously true. Such a
            // declaration has no production consumer either and belongs in the same census.
            .Where(static candidate => !candidate.IsRuntimeEntryPoint
                && candidate.ReferencePaths.All(IsTestPath))
            .Select(candidate => new ProductionTestOnlyTypeFinding(
                candidate.QualifiedName,
                candidate.Symbol.Name,
                candidate.DeclarationPaths.Order(StringComparer.Ordinal).ToArray(),
                candidate.ReferencePaths.Order(StringComparer.Ordinal).ToArray(),
                Allowlist.GetValueOrDefault(candidate.QualifiedName)))
            .OrderBy(static finding => finding.QualifiedName, StringComparer.Ordinal)
            .ToArray();
    }

    private static Dictionary<INamedTypeSymbol, CandidateType> CollectCandidates(
        CSharpCompilation compilation,
        IEnumerable<SourceFile> sources)
    {
        var candidates = new Dictionary<INamedTypeSymbol, CandidateType>(
            SymbolEqualityComparer.Default);

        foreach (var source in sources.Where(static source => IsProductionPath(source.Path)))
        {
            var model = compilation.GetSemanticModel(source.Tree);
            var root = source.Tree.GetRoot();
            var declarations = root.DescendantNodes().OfType<BaseTypeDeclarationSyntax>()
                .Select(declaration => model.GetDeclaredSymbol(declaration))
                .Concat(root.DescendantNodes().OfType<DelegateDeclarationSyntax>()
                    .Select(declaration => model.GetDeclaredSymbol(declaration)))
                .OfType<INamedTypeSymbol>()
                // A C# 14 extension(Receiver) { } block declares a synthesized extension
                // grouping type. It is a compiler implementation detail of the enclosing static
                // class, not a user production type that could be independently dead; its
                // members' reachability is attributed to that enclosing class in CollectReferences.
                .Where(static symbol => !symbol.IsExtension);

            foreach (var declaration in declarations)
            {
                var symbol = declaration.OriginalDefinition;
                if (!candidates.TryGetValue(symbol, out var candidate))
                {
                    candidate = new CandidateType(
                        symbol,
                        QualifiedName(symbol),
                        IsRuntimeEntryPoint(symbol));
                    candidates.Add(symbol, candidate);
                }

                candidate.DeclarationPaths.Add(source.Path);
            }
        }

        // Partial types have several syntax declarations but one INamedTypeSymbol. Grouping by
        // that symbol above prevents another partial declaration from being mistaken for a use.
        // Dunet's *0MatchExtensions types are generated from [Union] and have no independent
        // tracked declaration, so they never enter this source-declaration candidate set.
        return candidates;
    }

    private static void CollectReferences(
        CSharpCompilation compilation,
        IEnumerable<SourceFile> sources,
        IReadOnlyDictionary<INamedTypeSymbol, CandidateType> candidates)
    {
        foreach (var source in sources)
        {
            var model = compilation.GetSemanticModel(source.Tree);
            var root = source.Tree.GetRoot();

            foreach (var name in root.DescendantNodes().OfType<SimpleNameSyntax>())
            {
                // Semantic binding distinguishes a type reference from a same-spelled method
                // group such as Select(EvidenceElement) or OrderBy(RoleOrder).
                var referencedType = ReferencedType(model.GetSymbolInfo(name).Symbol);
                AddReference(candidates, referencedType, source.Path);
            }

            foreach (var invocation in root.DescendantNodes().OfType<InvocationExpressionSyntax>())
            {
                var method = model.GetSymbolInfo(invocation).Symbol as IMethodSymbol;
                var extension = method?.ReducedFrom
                    ?? (method?.IsExtensionMethod is true ? method : null);

                // Extension containers are used through member syntax, so their class name need
                // not appear at the call site. Attribute the bound extension call to its class.
                AddReference(candidates, extension?.ContainingType, source.Path);

                // C# 14 static extension members (extension(Receiver) { static Member }) are
                // invoked as Receiver.Member(...) and never reduce, so ReducedFrom/IsExtensionMethod
                // above miss them. The member's containing type is the synthesized extension
                // grouping, whose own containing type is the user-visible static class. Attribute
                // the call to that class so it is not misread as a test-only production type — but
                // only for EXTERNAL incoming edges: a member calling a sibling member of the same
                // enclosing class is an internal edge and must not keep an otherwise-dead container
                // alive, exactly as an ordinary type's internal self-calls do not.
                var container = method?.ContainingType;
                if (container?.IsExtension is true
                    && !EnclosedBy(model.GetEnclosingSymbol(invocation.SpanStart), container.ContainingType))
                {
                    AddReference(candidates, container.ContainingType, source.Path);
                }
            }
        }

        // xUnit test classes are reflection entry points, but candidate collection is restricted
        // to the three production assembly roots; test-only declarations are therefore excluded
        // before reference classification rather than treated as dead production types.
    }

    private static INamedTypeSymbol? ReferencedType(ISymbol? symbol) => symbol switch
    {
        INamedTypeSymbol type => type.OriginalDefinition,
        IAliasSymbol { Target: INamedTypeSymbol type } => type.OriginalDefinition,
        _ => null,
    };

    private static void AddReference(
        IReadOnlyDictionary<INamedTypeSymbol, CandidateType> candidates,
        INamedTypeSymbol? symbol,
        string path)
    {
        if (symbol is not null
            && candidates.TryGetValue(symbol.OriginalDefinition, out var candidate))
        {
            candidate.ReferencePaths.Add(path);
        }
    }

    // True when the call-site symbol is lexically inside container (walking out through any
    // synthesized C# 14 extension grouping). Used to reject internal self-edges when crediting an
    // extension member invocation to its user-visible enclosing class.
    private static bool EnclosedBy(ISymbol? callSite, INamedTypeSymbol? container)
    {
        if (container is null)
        {
            return false;
        }

        for (var type = callSite as INamedTypeSymbol ?? callSite?.ContainingType;
            type is not null;
            type = type.ContainingType)
        {
            if (SymbolEqualityComparer.Default.Equals(
                type.OriginalDefinition,
                container.OriginalDefinition))
            {
                return true;
            }
        }

        return false;
    }

    private static IEnumerable<MetadataReference> PlatformReferences()
    {
        var paths = AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") as string
            ?? throw new InvalidOperationException(
                "The runtime did not expose TRUSTED_PLATFORM_ASSEMBLIES for Roslyn analysis.");

        return paths.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Distinct(StringComparer.Ordinal)
            .Select(static path => MetadataReference.CreateFromFile(path));
    }

    private static SyntaxTree ImplicitUsingsTree() => CSharpSyntaxTree.ParseText(
        """
        global using System;
        global using System.Collections.Generic;
        global using System.IO;
        global using System.Linq;
        global using System.Net.Http;
        global using System.Threading;
        global using System.Threading.Tasks;
        """,
        CSharpParseOptions.Default.WithLanguageVersion(LanguageVersion.Preview),
        "ImplicitUsings.g.cs");

    private static string QualifiedName(INamedTypeSymbol symbol) =>
        symbol.ToDisplayString(SymbolDisplayFormat.CSharpErrorMessageFormat);

    private static bool IsRuntimeEntryPoint(INamedTypeSymbol symbol) =>
        symbol.GetMembers("Main").OfType<IMethodSymbol>().Any(static method =>
            method.IsStatic
            && method.DeclaredAccessibility == Accessibility.Public
            && (method.ReturnsVoid
                || method.ReturnType.SpecialType == SpecialType.System_Int32
                || method.ReturnType.Name == "Task")
            && (method.Parameters.Length == 0
                || method.Parameters is
                [
                    {
                        Type: IArrayTypeSymbol
                        {
                            ElementType.SpecialType: SpecialType.System_String,
                        },
                    },
                ]));

    private static bool IsProductionPath(string path) =>
        ProductionPrefixes.Any(prefix => path.StartsWith(prefix, StringComparison.Ordinal));

    private static bool IsTestPath(string path) =>
        path.StartsWith("tools/tests/", StringComparison.Ordinal);

    private sealed record SourceFile(string Path, SyntaxTree Tree);

    private sealed class CandidateType(
        INamedTypeSymbol symbol,
        string qualifiedName,
        bool isRuntimeEntryPoint)
    {
        internal INamedTypeSymbol Symbol { get; } = symbol;
        internal string QualifiedName { get; } = qualifiedName;
        // Main is reached by the .NET host rather than another source declaration. Treating the
        // host boundary as no consumer would falsely classify the executable's entry point.
        internal bool IsRuntimeEntryPoint { get; } = isRuntimeEntryPoint;
        internal HashSet<string> DeclarationPaths { get; } = new(StringComparer.Ordinal);
        internal HashSet<string> ReferencePaths { get; } = new(StringComparer.Ordinal);
    }
}
