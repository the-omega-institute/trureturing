using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

internal static class LeanReportFixture
{
    public static LeanAxiomReport ForDocuments(IEnumerable<ScribeDocument> documents)
    {
        var declarations = documents
            .SelectMany(static document => References(document.Content))
            .Distinct()
            .GroupBy(static reference => reference.Reference.Path.Value, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => new LeanFileReport(
                    [],
                        group.Select(static reference => new LeanDeclaration(
                            Selector(reference),
                            ReportKind(reference.ExpectedKind),
                            $"statement-v1(source={reference.Value})",
                            ImmutableArray.Create("propext", "Classical.choice", "Quot.sound")))
                        .ToImmutableArray()),
                StringComparer.Ordinal);
        return LeanAxiomReport.Create(declarations);
    }

    private static IEnumerable<LeanDeclarationRef> References(BlockSequence content)
    {
        foreach (var block in content.Items)
        {
            switch (block)
            {
                case DocumentBlock.Section section:
                    foreach (var reference in References(section.Content)) yield return reference;
                    break;
                case DocumentBlock.Describe describe:
                    if (describe.Statement is DescribeStatement.LeanDeclaration lean)
                    {
                        yield return lean.Value;
                    }
                    foreach (var reference in References(describe.Content)) yield return reference;
                    break;
            }
        }
    }

    private static string Selector(LeanDeclarationRef reference) =>
        reference.Value.Replace('/', '.');

    private static string ReportKind(LeanDeclarationKind? kind) => kind switch
    {
        null => "theorem",
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
