using System.Collections.Immutable;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.TestSupport;

internal static class LeanReportFixture
{
    public static LeanAxiomReport ForDocuments(IEnumerable<ScribeDocument> documents)
    {
        var declarations = documents
            .SelectMany(static document => References(document.Content))
            .DistinctBy(static item => item.Reference.Value, StringComparer.Ordinal)
            .GroupBy(static item => item.Reference.Reference.Path.Value, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => new LeanFileReport(
                    [],
                        group.Select(static item => new LeanDeclaration(
                            Selector(item.Reference),
                            item.ReportKind,
                            $"statement-v1(source={item.Reference.Value})",
                            ImmutableArray.Create("propext", "Classical.choice", "Quot.sound")))
                        .ToImmutableArray()),
                StringComparer.Ordinal);
        return LeanAxiomReport.Create(declarations);
    }

    // The kind a synthetic report should claim used to be read off the reference, which carried an
    // author-supplied ExpectedKind. That field is gone — a declaration's kind is the report's to
    // state — so the fixture takes it from the node instead: its authored kind, or the role a
    // report-derived node was given.
    private readonly record struct ReferencedDeclaration(LeanDeclarationRef Reference, string ReportKind);

    private static IEnumerable<ReferencedDeclaration> References(BlockSequence content)
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
                        yield return new ReferencedDeclaration(lean.Value, ReportKindOf(describe));
                    }
                    foreach (var reference in References(describe.Content)) yield return reference;
                    break;
            }
        }
    }

    private static string Selector(LeanDeclarationRef reference) =>
        reference.Value.Replace('/', '.');

    private static string ReportKindOf(DocumentBlock.Describe describe) => describe.KindSource switch
    {
        DescribeKindSource.Authored authored => ReportKind(authored.Value),
        DescribeKindSource.ReportDerived derived => derived.Role switch
        {
            DescribeRole.Definition => "def",
            DescribeRole.Theorem => "theorem",
            DescribeRole.Proposition => "theorem",
            DescribeRole.Lemma => "theorem",
            DescribeRole.Remark => "theorem",
            _ => "theorem",
        },
        _ => "theorem",
    };

    private static string ReportKind(DescribeKind kind) => kind switch
    {
        DescribeKind.Definition => "def",
        DescribeKind.Theorem => "theorem",
        DescribeKind.Proposition => "theorem",
        DescribeKind.Lemma => "theorem",
        DescribeKind.Example => "theorem",
        DescribeKind.Remark => "theorem",
        _ => throw new ArgumentOutOfRangeException(nameof(kind)),
    };
}
