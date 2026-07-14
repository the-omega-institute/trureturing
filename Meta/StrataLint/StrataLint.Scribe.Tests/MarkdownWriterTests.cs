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
                        new DocumentBlock.Proposition(
                            Heading.Create("Formula"),
                            LeanDeclarationRef.Create(
                                "D5/S1/Scale/Embedding.embedding_apply"),
                            BlockSequence.Create([paragraph])),
                        new DocumentBlock.Theorem(
                            Heading.Create("Injectivity"),
                            LeanDeclarationRef.Create(
                                "D5/S1/Scale/Embedding.embedding_injective"),
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
            + "Lean declaration: `D5/S1/Scale/Embedding.embedding_apply` `✓ std3`\n\n"
            + "Map $\\varphi$ mirrors `D5/B/S1/Scale/Embedding`.\n\n"
            + "### Theorem: Injectivity\n\n"
            + "Lean declaration: `D5/S1/Scale/Embedding.embedding_injective` `✓ std3`\n\n"
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
