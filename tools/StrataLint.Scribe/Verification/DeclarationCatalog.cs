using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public sealed record ResolvedDeclaration(
    DeclarationHandle Handle,
    LeanDeclaration Declaration,
    LeanDeclarationKind FormalKind,
    DescribeKind? Kind,
    bool IsSorryFree,
    string AxiomBadge);

public sealed class DeclarationCatalog
{
    private readonly ImmutableDictionary<RepoPath,
        ImmutableDictionary<string, ImmutableArray<IndexedDeclaration>>> modules;
    private readonly ImmutableDictionary<RepoPath, ImmutableArray<string>> imports;

    private DeclarationCatalog(
        ImmutableDictionary<RepoPath,
            ImmutableDictionary<string, ImmutableArray<IndexedDeclaration>>> modules,
        ImmutableDictionary<RepoPath, ImmutableArray<string>> imports) =>
        (this.modules, this.imports) = (modules, imports);

    public static DeclarationCatalog Create(LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(report);
        var modules = ImmutableDictionary.CreateBuilder<RepoPath,
            ImmutableDictionary<string, ImmutableArray<IndexedDeclaration>>>();
        var imports = ImmutableDictionary.CreateBuilder<RepoPath, ImmutableArray<string>>();
        foreach (var (path, module) in report.Files)
        {
            if (!string.IsNullOrEmpty(module.Error))
            {
                throw new InvalidOperationException(
                    $"Lean compiled-artifact report failed for {path.Value}: {module.Error}");
            }
            modules.Add(
                path,
                module.Declarations
                    .Select(declaration => Index(path, declaration))
                    .GroupBy(static declaration => declaration.Declaration.Name, StringComparer.Ordinal)
                    .ToImmutableDictionary(
                        static group => group.Key,
                        static group => group.ToImmutableArray(),
                        StringComparer.Ordinal));
            imports.Add(path, module.Imports);
        }
        return new DeclarationCatalog(modules.ToImmutable(), imports.ToImmutable());
    }

    public ResolvedDeclaration Resolve(DeclarationHandle handle)
    {
        var path = handle.Reference?.Path
            ?? throw new InvalidOperationException("An uninitialized declaration handle is invalid.");
        if (!modules.TryGetValue(path, out var declarations))
        {
            throw new InvalidOperationException(
                $"Lean compiled-artifact report does not contain module {path.Value} for {handle.Value}.");
        }
        var declarationName = handle.Value[(handle.Value.LastIndexOf('.') + 1)..];
        var suffix = "." + declarationName;
        var matches = declarations
            .Where(entry =>
                string.Equals(entry.Key, declarationName, StringComparison.Ordinal)
                || entry.Key.EndsWith(suffix, StringComparison.Ordinal))
            .SelectMany(static entry => entry.Value)
            .ToArray();
        if (matches.Length == 0)
        {
            throw new InvalidOperationException(
                $"Lean compiled-artifact report for {path.Value} does not contain {handle.Value}.");
        }
        if (matches.Length != 1)
        {
            throw new InvalidOperationException(
                $"Lean compiled-artifact report resolves {handle.Value} ambiguously.");
        }
        var item = matches[0];
        if (item.Declaration.Axioms.Contains("sorryAx", StringComparer.Ordinal))
        {
            throw new InvalidOperationException(
                $"Lean declaration {handle.Value} is not sorry-free according to the compiled report.");
        }
        return new ResolvedDeclaration(
            handle, item.Declaration, item.FormalKind, item.Kind, true, item.AxiomBadge);
    }

    internal DescribeKind ResolveKind(DocumentBlock.Describe describe) => describe.KindSource switch
    {
        DescribeKindSource.Authored authored => authored.Value,
        DescribeKindSource.ReportDerived derived => ResolveNarrativeKind(Resolve(derived.Handle).Kind, derived.Role),
        _ => throw new InvalidOperationException("Unknown Describe kind source."),
    };

    internal ImmutableArray<string> ImportsFor(RepoPath modulePath) =>
        imports.TryGetValue(modulePath, out var moduleImports) ? moduleImports : [];

    internal IEnumerable<LeanDeclaration> Declarations => modules.Values
        .SelectMany(static module => module.Values)
        .SelectMany(static declarations => declarations)
        .Select(static declaration => declaration.Declaration);

    private static IndexedDeclaration Index(RepoPath path, LeanDeclaration declaration)
    {
        if (string.IsNullOrWhiteSpace(declaration.Name)
            || string.IsNullOrWhiteSpace(declaration.Kind)
            || !FrozenHashSyntax.IsSha256(declaration.StatementTypeAddress)
            || declaration.Axioms.Any(string.IsNullOrWhiteSpace))
        {
            throw new InvalidOperationException(
                $"Lean compiled-artifact report is malformed for {path.Value}.");
        }
        var (formalKind, kind) = declaration.Kind switch
        {
            "def" => (LeanDeclarationKind.Definition, (DescribeKind?)DescribeKind.Definition),
            "theorem" => (LeanDeclarationKind.Theorem, DescribeKind.Theorem),
            "axiom" => (LeanDeclarationKind.Axiom, null),
            "opaque" => (LeanDeclarationKind.Opaque, null),
            "quotient" => (LeanDeclarationKind.Quotient, null),
            "constructor" => (LeanDeclarationKind.Constructor, null),
            "recursor" => (LeanDeclarationKind.Recursor, null),
            "inductive" => (LeanDeclarationKind.Inductive, null),
            _ => throw new InvalidOperationException(
                $"Lean declaration {declaration.Name} has unsupported kind {declaration.Kind}."),
        };
        var nonstandard = declaration.Axioms.Where(static axiom => !LeanAxiomFacts.IsStandard(axiom))
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        return new IndexedDeclaration(
            declaration, formalKind, kind,
            nonstandard.Length == 0 ? "✓ std3" : "⚠ " + string.Join(", ", nonstandard));
    }

    private static DescribeKind ResolveNarrativeKind(DescribeKind? reportKind, DescribeRole? role) => role switch
    {
        null => reportKind ?? throw new InvalidOperationException(
            "The resolved Lean declaration kind cannot be projected to a Describe kind without an explicit role."),
        DescribeRole.Definition => DescribeKind.Definition,
        DescribeRole.Theorem => DescribeKind.Theorem,
        DescribeRole.Proposition => DescribeKind.Proposition,
        DescribeRole.Lemma => DescribeKind.Lemma,
        DescribeRole.Remark => DescribeKind.Remark,
        _ => throw new ArgumentOutOfRangeException(nameof(role)),
    };

    private sealed record IndexedDeclaration(
        LeanDeclaration Declaration,
        LeanDeclarationKind FormalKind,
        DescribeKind? Kind,
        string AxiomBadge);
}
