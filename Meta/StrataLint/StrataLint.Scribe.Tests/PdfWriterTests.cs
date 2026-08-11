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
                DocumentBlock.Describe.Example(
                    DescribeId.Create("golden-identity"),
                    Heading.Create("Golden identity"),
                    new Formula.Phi(),
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
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("critical-line"),
                    Heading.Create("Critical line"),
                    LeanDeclarationRef.Create(
                        "D5/S1/Scale/Embedding.embedding_injective"),
                    CriticalLineFormula(),
                    DescribeProvenance.RepoDerived(),
                    BlockSequence.Create(
                    [
                        DefinitionDsl.Paragraph(DefinitionDsl.Text("Commentary.")),
                    ])
                ),
            ]));

        var pdf = QuestPdfWriter.Write(document, LeanReportFixture.ForDocuments([document]));

        Assert.True(pdf.Length > 5);
        Assert.Equal("%PDF-", Encoding.ASCII.GetString(pdf.AsSpan()[..5]));
    }

    private static Formula CriticalLineFormula() => new Formula.Layout(
        FormulaLayoutMode.Inline,
        new Formula.Relation(
            new Formula.FunctionCall(
                FormulaIdentifier.Create("Re"),
                [new Formula.Symbol(FormulaIdentifier.Create("s"))]),
            FormulaRelationOperator.Equal,
            new Formula.Fraction(new Formula.Number(1), new Formula.Number(2))));

    [Fact]
    public void QuestPdfWriterCompilesAcademicLiteratureCitations()
    {
        var reference = LibraryNoteRef.Create("D5/L/sos1957threegap");
        var document = ScribeDocument.Create(
            DefinitionDsl.Header("D5/S1/Scale/Embedding", "Academic citation fixture."),
            Heading.Create("Academic citation"),
            BlockSequence.Create(
            [
                DocumentBlock.Describe.Remark(
                    DescribeId.Create("three-gap-context"),
                    Heading.Create("Three-gap context"),
                    DescribeStatement.FromFormula(new Formula.Phi()),
                    DescribeProvenance.LiteratureAttested(reference),
                    BlockSequence.Create(
                    [
                        DefinitionDsl.Paragraph(DefinitionDsl.Text("Referenced context.")),
                    ])
                ),
            ]));
        var citations = new Dictionary<string, LiteratureCitation>(StringComparer.Ordinal)
        {
            ["sos1957threegap"] = LiteratureCitation.Create(
                "Vera T. Sos",
                1957,
                "On the three gap theorem",
                "10.1007/BF01389053"),
        };

        var pdf = QuestPdfWriter.Write(document, citations: citations);

        Assert.True(pdf.Length > 5);
        Assert.Equal("%PDF-", Encoding.ASCII.GetString(pdf.AsSpan()[..5]));
    }

}
