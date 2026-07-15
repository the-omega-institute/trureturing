using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class MarkdownWriterTests
{
    [Fact]
    public void WriterEmitsTheCanonicalMarkdownLayout()
    {
        var paragraph = Paragraph(
            new Inline.Text(TextRun.Create("Map ")),
            new Inline.InlineFormula(new Formula.Phi()),
            new Inline.Text(TextRun.Create(" mirrors ")),
            new Inline.GidReference(GidRef.Create("D5/B/S1/Scale/Embedding")),
            new Inline.Text(TextRun.Create(".")));
        Formula identity = new Formula.Relation(
            new Formula.Power(new Formula.Phi(), new Formula.Number(2)),
            FormulaRelationOperator.Equal,
            new Formula.Binary(
                new Formula.Phi(),
                FormulaBinaryOperator.Add,
                new Formula.Number(1)));
        var document = ScribeDocument.Create(
            CreateHeader(),
            Heading.Create("Sample"),
            BlockSequence.Create(
            [
                paragraph,
                new DocumentBlock.DisplayFormula(identity),
                new DocumentBlock.Section(
                    Heading.Create("Results"),
                    BlockSequence.Create(
                    [
                        new DocumentBlock.Describe(
                            DescribeId.Create("formula"),
                            DescribeKind.Proposition,
                            Heading.Create("Formula"),
                            DescribeStatement.FromFormula(identity),
                            DescribeProvenance.RepoDerived(),
                            BlockSequence.Create([paragraph])),
                        new DocumentBlock.Describe(
                            DescribeId.Create("injectivity"),
                            DescribeKind.Theorem,
                            Heading.Create("Injectivity"),
                            DescribeStatement.FromLean(LeanDeclarationRef.Create(
                                "D5/S1/Scale/Embedding.embedding_injective")),
                            DescribeProvenance.RepoDerived(),
                            BlockSequence.Create([paragraph])),
                    ])),
            ]));

        var report = LeanReportFixture.ForDocuments([document]);
        var text = Encoding.UTF8.GetString(CanonicalMarkdownWriter.Write(document, report).AsSpan());

        Assert.Equal(
            "# Sample\n\n"
            + "Map $\\varphi$ mirrors `D5/B/S1/Scale/Embedding`.\n\n"
            + "$$\n\\varphi^{2} = \\varphi + 1\n$$\n\n"
            + "## Results\n\n"
            + "### Proposition: Formula\n\n"
            + "Provenance: `repo-derived`\n\n"
            + "Statement:\n\n"
            + "$$\n\\varphi^{2} = \\varphi + 1\n$$\n\n"
            + "Map $\\varphi$ mirrors `D5/B/S1/Scale/Embedding`.\n\n"
            + "### Theorem: Injectivity\n\n"
            + "Provenance: `repo-derived`\n\n"
            + "Statement: `D5/S1/Scale/Embedding.embedding_injective` `✓ std3`\n\n"
            + "Map $\\varphi$ mirrors `D5/B/S1/Scale/Embedding`.\n",
            text);
    }

    [Fact]
    public void WriterAlwaysEmitsTheSameStrictUtf8Bytes()
    {
        var document = ScribeDocument.Create(
            CreateHeader(),
            Heading.Create("Sample"),
            BlockSequence.Create([Paragraph(new Inline.Text(TextRun.Create("Stable.")))]));

        var first = CanonicalMarkdownWriter.Write(document);
        var second = CanonicalMarkdownWriter.Write(document);
        var text = Encoding.UTF8.GetString(first.AsSpan());

        Assert.Equal(first.ToArray(), second.ToArray());
        Assert.False(first.AsSpan().StartsWith(Encoding.UTF8.Preamble));
        Assert.DoesNotContain('\r', text);
        Assert.EndsWith("\n", text, StringComparison.Ordinal);
        Assert.False(text.EndsWith("\n\n", StringComparison.Ordinal));
    }

    [Fact]
    public void LiteratureProvenanceEmitsOnlyTypedReferencesNotCopiedMetadata()
    {
        var reference = LibraryNoteRef.Create("D5/L/sos1957threegap");
        var document = ScribeDocument.Create(
            CreateHeader(),
            Heading.Create("Literature sample"),
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
                        Paragraph(new Inline.Text(TextRun.Create("Referenced context."))),
                    ])),
            ]));

        var text = Encoding.UTF8.GetString(CanonicalMarkdownWriter.Write(document).AsSpan());

        Assert.Contains(
            "Provenance: `literature-attested` via `D5/L/sos1957threegap` (`lit/sos1957threegap`)",
            text,
            StringComparison.Ordinal);
        Assert.DoesNotContain("On the three gap theorem", text, StringComparison.Ordinal);
        Assert.DoesNotContain("10.1007", text, StringComparison.Ordinal);
    }

    private static DocumentBlock Paragraph(params Inline[] content) =>
        new DocumentBlock.Paragraph(InlineSequence.Create(content));

    private static DocumentHeader CreateHeader() => DocumentHeader.Create(
        GidRef.Create("D5/S1/Scale/Embedding"),
        Generality.Instance,
        GidRef.Create("D5/B/S1/Scale/Embedding"),
        new EvidenceMirror.Waiver(WaiverReason.Create("algebraically-proved")),
        [Anchor.ParseCanonical("mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf")],
        Digest.Create("The real embedding is injective."));
}
