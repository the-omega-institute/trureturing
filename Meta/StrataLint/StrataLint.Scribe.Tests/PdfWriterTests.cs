using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class PdfWriterTests
{
    [Fact]
    public void QuestPdfWriterRendersDescribeNodes()
    {
        var document = ScribeDocument.Create(
            DefinitionDsl.Header("D5/S1/Scale/Embedding", "Describe PDF fixture."),
            Heading.Create("Describe PDF"),
            BlockSequence.Create(
            [
                new DocumentBlock.Describe(
                    DescribeId.Create("golden-identity"),
                    DescribeKind.Lemma,
                    Heading.Create("Golden identity"),
                    DescribeStatement.FromFormula(new Formula.Phi()),
                    DescribeProvenance.RepoDerived(),
                    BlockSequence.Create(
                    [
                        DefinitionDsl.Paragraph(DefinitionDsl.Text("Typed content.")),
                    ])),
            ]));

        var pdf = QuestPdfWriter.Write(document);

        Assert.True(pdf.Length > 5);
        Assert.Equal("%PDF-", Encoding.ASCII.GetString(pdf.AsSpan()[..5]));
    }

    [Fact]
    public void QuestPdfWriterCompilesLeanDescribeWithExplicitLatex()
    {
        var document = ScribeDocument.Create(
            DefinitionDsl.Header("D5/S1/Scale/Embedding", "Describe PDF LaTeX fixture."),
            Heading.Create("Describe PDF LaTeX"),
            BlockSequence.Create(
            [
                new DocumentBlock.Describe(
                    DescribeId.Create("critical-line"),
                    DescribeKind.Theorem,
                    Heading.Create("Critical line"),
                    DescribeStatement.FromLean(LeanDeclarationRef.Create(
                        "D5/S1/Scale/Embedding.embedding_injective")),
                    DescribeProvenance.RepoDerived(),
                    BlockSequence.Create(
                    [
                        DefinitionDsl.Paragraph(DefinitionDsl.Text("Commentary.")),
                    ]),
                    LatexStatement.Create("$\\operatorname{Re}(s) = \\frac{1}{2}$")),
            ]));

        var pdf = QuestPdfWriter.Write(document, LeanReportFixture.ForDocuments([document]));

        Assert.True(pdf.Length > 5);
        Assert.Equal("%PDF-", Encoding.ASCII.GetString(pdf.AsSpan()[..5]));
    }

    [Fact]
    public void QuestPdfWriterGeneratesEachPilotWithAPdfHeader()
    {
        var report = LeanReportFixture.ForDocuments(
            DocumentDefinitions.All.Select(static definition => definition.Document));
        foreach (var definition in DocumentDefinitions.All)
        {
            var pdf = QuestPdfWriter.Write(definition.Document, report);

            Assert.True(pdf.Length > 5);
            Assert.Equal("%PDF-", Encoding.ASCII.GetString(pdf.AsSpan()[..5]));
        }
    }
}
