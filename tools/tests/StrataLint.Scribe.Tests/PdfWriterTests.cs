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
                Describe.Example(
                    DescribeId.Create("golden-identity"),
                    Heading.Create("Golden identity"),
                    new Formula.Phi(),
                    AssessedProvenance.FromRepo(),
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
                Describe.Lean(
                    DescribeId.Create("critical-line"),
                    DeclarationHandle.Create(
                        "D5/S1/Scale/Embedding.embedding_injective"),
                    Heading.Create("Critical line"),
                    StatementSource.FromAuthor(CriticalLineFormula()),
                    AssessedProvenance.FromRepo(),
                    BlockSequence.Create(
                    [
                        DefinitionDsl.Paragraph(DefinitionDsl.Text("Commentary.")),
                    ]),
                    DescribeRole.Theorem
                ),
            ]));

        var pdf = QuestPdfWriter.Write(
            document, DeclarationCatalog.Create(LeanReportFixture.ForDocuments([document])));

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

    [Theory]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public void QuestPdfWriterCompilesAcademicLiteratureCitations(bool useDoi, bool useUrl)
    {
        var reference = LibraryNoteRef.Create("D5/L/sos1957threegap");
        var document = ScribeDocument.Create(
            DefinitionDsl.Header("D5/S1/Scale/Embedding", "Academic citation fixture."),
            Heading.Create("Academic citation"),
            BlockSequence.Create(
            [
                Describe.Remark(
                    DescribeId.Create("three-gap-context"),
                    Heading.Create("Three-gap context"),
                    new Formula.Phi(),
                    AssessedProvenance.FromLiterature(reference),
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
                useDoi ? "10.1007/BF01389053" : null,
                useUrl ? "https://example.org/source" : null),
        };

        var pdf = QuestPdfWriter.Write(document, citations: citations);

        Assert.Equal(
            "Citation. Vera T. Sos (1957). On the three gap theorem. "
            + (useDoi ? "DOI: https://doi.org/10.1007/BF01389053." : string.Empty)
            + (useDoi && useUrl ? " " : string.Empty)
            + (useUrl ? "URL: https://example.org/source." : string.Empty),
            QuestPdfWriter.AcademicReferenceLine("Citation", reference, citations));
        Assert.True(pdf.Length > 5);
        Assert.Equal("%PDF-", Encoding.ASCII.GetString(pdf.AsSpan()[..5]));
    }

}
