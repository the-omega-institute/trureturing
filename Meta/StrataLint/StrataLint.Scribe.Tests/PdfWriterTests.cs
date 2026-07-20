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
    public void QuestPdfWriterCompilesAcademicLiteratureCitations()
    {
        var reference = LibraryNoteRef.Create("D5/L/sos1957threegap");
        var document = ScribeDocument.Create(
            DefinitionDsl.Header("D5/S1/Scale/Embedding", "Academic citation fixture."),
            Heading.Create("Academic citation"),
            BlockSequence.Create(
            [
                new DocumentBlock.Describe(
                    DescribeId.Create("three-gap-context"),
                    DescribeKind.Remark,
                    Heading.Create("Three-gap context"),
                    DescribeStatement.FromFormula(new Formula.Phi()),
                    DescribeProvenance.LiteratureAttested(reference),
                    BlockSequence.Create(
                    [
                        DefinitionDsl.Paragraph(DefinitionDsl.Text("Referenced context.")),
                    ])),
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

    [Fact]
    public void QuestPdfWriterGeneratesEachPilotWithAPdfHeader()
    {
        var report = LeanReportFixture.ForDocuments(
            DocumentDefinitions.All.Select(static definition => definition.Document));
        var citations = LibraryNoteCatalog.Load(FindRepositoryRoot()).Citations;
        foreach (var definition in DocumentDefinitions.All)
        {
            var pdf = QuestPdfWriter.Write(definition.Document, report, citations);

            Assert.True(pdf.Length > 5);
            Assert.Equal("%PDF-", Encoding.ASCII.GetString(pdf.AsSpan()[..5]));
        }
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "global.json"))
                && Directory.Exists(Path.Combine(current.FullName, "Library")))
            {
                return current.FullName;
            }
        }

        throw new InvalidOperationException("repository root was not found above the test base directory");
    }
}
