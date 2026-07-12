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
                            "theorem",
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
                case DocumentBlock.Proposition proposition:
                    yield return proposition.Declaration;
                    foreach (var reference in References(proposition.Content)) yield return reference;
                    break;
                case DocumentBlock.Theorem theorem:
                    yield return theorem.Declaration;
                    foreach (var reference in References(theorem.Content)) yield return reference;
                    break;
                case DocumentBlock.RenderedStatement statement:
                    yield return statement.Declaration;
                    break;
            }
        }
    }

    private static string Selector(LeanDeclarationRef reference) =>
        reference.Value[(reference.Value.LastIndexOf('.') + 1)..];
}
