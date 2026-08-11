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
    internal LeanAxiomReport SourceReport { get; }

    private readonly ImmutableDictionary<RepoPath,
        ImmutableDictionary<string, ImmutableArray<IndexedDeclaration>>> modules;

    private DeclarationCatalog(
        LeanAxiomReport sourceReport,
        ImmutableDictionary<RepoPath,
            ImmutableDictionary<string, ImmutableArray<IndexedDeclaration>>> modules) =>
        (SourceReport, this.modules) = (sourceReport, modules);

    public static DeclarationCatalog Create(LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(report);
        var modules = ImmutableDictionary.CreateBuilder<RepoPath,
            ImmutableDictionary<string, ImmutableArray<IndexedDeclaration>>>();
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
        }
        return new DeclarationCatalog(report, modules.ToImmutable());
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
        var name = handle.Value.Replace('/', '.');
        if (!declarations.TryGetValue(name, out var matches))
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

    private static IndexedDeclaration Index(RepoPath path, LeanDeclaration declaration)
    {
        if (string.IsNullOrWhiteSpace(declaration.Name)
            || string.IsNullOrWhiteSpace(declaration.Kind)
            || string.IsNullOrWhiteSpace(declaration.TypeRepresentation)
            || declaration.TypeRepresentation.IndexOfAny(['\r', '\n', '`']) >= 0
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
        _ => throw new ArgumentOutOfRangeException(nameof(role)),
    };

    private sealed record IndexedDeclaration(
        LeanDeclaration Declaration,
        LeanDeclarationKind FormalKind,
        DescribeKind? Kind,
        string AxiomBadge);
}
