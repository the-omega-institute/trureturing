using System.Collections.Immutable;
using System.Diagnostics;
using QuestPDF.Fluent;
using QuestPDF.Helpers;
using QuestPDF.Infrastructure;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class QuestPdfWriter
{
    private static readonly string[] MonospaceFonts =
    [
        "Courier New",
        "DejaVu Sans Mono",
        "Liberation Mono",
    ];

    public static ImmutableArray<byte> Write(
        ScribeDocument document,
        LeanAxiomReport? leanReport = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        QuestPDF.Settings.License = LicenseType.Community;

        var pdf = QuestPDF.Fluent.Document.Create(container =>
        {
            container.Page(page =>
            {
                page.Size(PageSizes.A4);
                page.Margin(36);
                page.PageColor(Colors.White);
                page.DefaultTextStyle(style => style.FontSize(10));

                page.Header().Column(header =>
                {
                    header.Item().Text(document.Title.Value).SemiBold().FontSize(19);
                    header.Item()
                        .Text(document.Header.Gid.Value)
                        .FontFamily(MonospaceFonts)
                        .FontSize(8);
                });

                page.Content().PaddingVertical(18).Column(column =>
                {
                    column.Spacing(8);
                    WriteBlocks(column, document.Content, 2, leanReport);
                });

                page.Footer()
                    .DefaultTextStyle(style => style.FontSize(8))
                    .AlignCenter()
                    .Text(text =>
                    {
                        text.Span("Page ");
                        text.CurrentPageNumber();
                    });
            });
        }).GeneratePdf();

        return ImmutableArray.CreateRange(pdf);
    }

    private static void WriteBlocks(
        ColumnDescriptor column,
        BlockSequence content,
        int headingLevel,
        LeanAxiomReport? leanReport)
    {
        foreach (var block in content.Items)
        {
            switch (block)
            {
                case DocumentBlock.Paragraph paragraph:
                    WriteParagraph(column, paragraph.Content);
                    break;
                case DocumentBlock.DisplayFormula display:
                    column.Item()
                        .Padding(6)
                        .Background(Colors.Grey.Lighten4)
                        .Text(LatexWriter.Write(display.Value))
                        .FontFamily(MonospaceFonts)
                        .FontSize(9);
                    break;
                case DocumentBlock.Section section:
                    WriteHeading(column, section.Title.Value, headingLevel);
                    WriteBlocks(column, section.Content, headingLevel + 1, leanReport);
                    break;
                case DocumentBlock.Describe describe:
                    WriteDescribe(column, describe, headingLevel, leanReport);
                    break;
                default:
                    throw new UnreachableException("Unknown document block.");
            }
        }
    }

    private static void WriteParagraph(ColumnDescriptor column, InlineSequence content)
    {
        column.Item().Text(text =>
        {
            foreach (var inline in content.Items)
            {
                switch (inline)
                {
                    case Inline.Text run:
                        text.Span(run.Run.Value);
                        break;
                    case Inline.InlineFormula formula:
                        text.Span($"${LatexWriter.Write(formula.Value)}$")
                            .FontFamily(MonospaceFonts);
                        break;
                    case Inline.GidReference reference:
                        text.Span(reference.Reference.Value)
                            .FontFamily(MonospaceFonts);
                        break;
                    default:
                        throw new UnreachableException("Unknown inline node.");
                }
            }
        });
    }

    private static void WriteDescribe(
        ColumnDescriptor column,
        DocumentBlock.Describe describe,
        int headingLevel,
        LeanAxiomReport? leanReport)
    {
        var kind = DescribeVocabulary.HeadingName(describe.Kind);
        var provenance = DescribeVocabulary.CanonicalName(describe.Provenance.Kind);
        if (describe.Provenance.LiteratureReference is { } literature)
        {
            provenance += $" via {literature.Value} ({literature.Anchor.CanonicalString})";
        }
        WriteHeading(column, $"{kind}: {describe.Title.Value}", headingLevel);
        column.Item().Text($"Provenance: {provenance}").FontSize(8);
        switch (describe.Statement)
        {
            case DescribeStatement.FormulaAst formula:
                column.Item()
                    .Padding(6)
                    .Background(Colors.Grey.Lighten4)
                    .Text(LatexWriter.Write(formula.Value))
                    .FontFamily(MonospaceFonts)
                    .FontSize(9);
                break;
            case DescribeStatement.LeanDeclaration lean:
                var verified = Resolve(lean.Value, leanReport);
                if (describe.StatementLatex is { } latex)
                {
                    column.Item()
                        .Padding(6)
                        .Background(Colors.Grey.Lighten4)
                        .Text(latex.Value)
                        .FontFamily(MonospaceFonts)
                        .FontSize(9);
                }
                column.Item()
                    .Text($"Lean: {lean.Value.Value} [{verified.AxiomBadge}]")
                    .FontFamily(MonospaceFonts)
                    .FontSize(8);
                break;
            default:
                throw new UnreachableException("Unknown Describe statement.");
        }

        WriteBlocks(column, describe.Content, headingLevel + 1, leanReport);
    }

    private static VerifiedLeanDeclaration Resolve(
        LeanDeclarationRef declaration,
        LeanAxiomReport? leanReport) =>
        LeanReferenceResolver.Resolve(
            declaration,
            leanReport ?? throw new InvalidOperationException(
                $"Lean compiled-artifact report is required for {declaration.Value}."));

    private static void WriteHeading(
        ColumnDescriptor column,
        string title,
        int headingLevel)
    {
        if (headingLevel > 6)
        {
            throw new InvalidOperationException("PDF heading depth exceeds level six.");
        }

        column.Item()
            .PaddingTop(headingLevel == 2 ? 8 : 4)
            .Text(title)
            .SemiBold()
            .FontSize(headingLevel == 2 ? 14 : 12);
    }
}
