using StrataLint.Engine;

namespace StrataLint.Scribe;

public sealed record VerifiedLeanDeclaration(
    LeanDeclarationRef Reference,
    LeanDeclaration Declaration,
    string AxiomBadge);

public static class LeanReferenceResolver
{
    public static VerifiedLeanDeclaration Resolve(
        LeanDeclarationRef reference,
        LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(reference);
        ArgumentNullException.ThrowIfNull(report);

        var modulePath = reference.Reference.Path;
        if (!report.Files.TryGetValue(modulePath, out var module))
        {
            throw new InvalidOperationException(
                $"Lean compiled-artifact report does not contain module {modulePath.Value} "
                + $"for {reference.Value}.");
        }

        if (!string.IsNullOrEmpty(module.Error))
        {
            throw new InvalidOperationException(
                $"Lean compiled-artifact report failed for {modulePath.Value}: {module.Error}");
        }

        var suffix = "." + reference.DeclarationName;
        var matches = module.Declarations
            .Where(declaration =>
                string.Equals(declaration.Name, reference.DeclarationName, StringComparison.Ordinal)
                || declaration.Name.EndsWith(suffix, StringComparison.Ordinal))
            .ToArray();
        if (matches.Length == 0)
        {
            throw new InvalidOperationException(
                $"Lean compiled-artifact report for {modulePath.Value} does not contain {reference.Value}.");
        }

        if (matches.Length != 1)
        {
            throw new InvalidOperationException(
                $"Lean compiled-artifact report resolves {reference.Value} ambiguously.");
        }

        var declaration = matches[0];
        if (reference.ExpectedKind is { } expectedKind)
        {
            var expected = ReportKind(expectedKind);
            if (!string.Equals(expected, declaration.Kind, StringComparison.Ordinal))
            {
                throw new InvalidOperationException(
                    $"Lean declaration {reference.Value} expected {expected}, found {declaration.Kind}.");
            }
        }

        if (reference.RequireNoSorry
            && declaration.Axioms.Contains("sorryAx", StringComparer.Ordinal))
        {
            throw new InvalidOperationException(
                $"Lean declaration {reference.Value} requires a sorry-free axiom closure, "
                + "but the compiled report contains sorryAx.");
        }

        if (string.IsNullOrWhiteSpace(declaration.TypeRepresentation)
            || declaration.TypeRepresentation.IndexOfAny(['\r', '\n', '`']) >= 0)
        {
            throw new InvalidOperationException(
                $"Lean declaration {reference.Value} has a malformed compiled TypeRepresentation.");
        }

        var nonstandard = declaration.Axioms
            .Where(static axiom => !LeanAxiomFacts.IsStandard(axiom))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var badge = nonstandard.Length == 0
            ? "✓ std3"
            : "⚠ " + string.Join(", ", nonstandard);
        return new VerifiedLeanDeclaration(reference, declaration, badge);
    }

    private static string ReportKind(LeanDeclarationKind kind) => kind switch
    {
        LeanDeclarationKind.Axiom => "axiom",
        LeanDeclarationKind.Definition => "def",
        LeanDeclarationKind.Theorem => "theorem",
        LeanDeclarationKind.Opaque => "opaque",
        LeanDeclarationKind.Quotient => "quotient",
        LeanDeclarationKind.Constructor => "constructor",
        LeanDeclarationKind.Recursor => "recursor",
        LeanDeclarationKind.Inductive => "inductive",
        _ => throw new ArgumentOutOfRangeException(nameof(kind)),
    };
}
