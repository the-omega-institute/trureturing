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
        // The kind assertion is gone rather than moved. It compared the report against a kind the
        // author typed at the call site; there is no longer an authored kind to compare, because the
        // catalog reads the declaration's kind from the report.
        //
        // The sorry check is now unconditional. It used to be opt-in through `requireNoSorry`, and
        // the only production caller never opted in, so it never ran. DeclarationCatalog.Resolve
        // already refuses a declaration whose axiom closure contains sorryAx; this path now agrees.
        if (declaration.Axioms.Contains("sorryAx", StringComparer.Ordinal))
        {
            throw new InvalidOperationException(
                $"Lean declaration {reference.Value} requires a sorry-free axiom closure, "
                + "but the compiled report contains sorryAx.");
        }

        var typeRepresentation = declaration.LoadTypeRepresentation();
        if (string.IsNullOrWhiteSpace(typeRepresentation)
            || typeRepresentation.IndexOfAny(['\r', '\n', '`']) >= 0)
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
}
