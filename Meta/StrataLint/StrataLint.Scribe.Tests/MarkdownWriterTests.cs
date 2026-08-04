using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class MarkdownWriterTests
{
    [Fact]
    public void WriterEmitsAcademicMarkdownWithAstNumberingAndLeanProofs()
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
                        DocumentBlock.Describe.Example(
                            DescribeId.Create("formula"),
                            Heading.Create("Formula"),
                            identity,
                            DescribeProvenance.RepoDerived(),
                            BlockSequence.Create([paragraph])),
                        DocumentBlock.Describe.Theorem(
                            DescribeId.Create("injectivity"),
                            Heading.Create("Injectivity"),
                            LeanDeclarationRef.Create(
                                "D5/S1/Scale/Embedding.embedding_injective"),
                            EmbedInjectiveFormula(),
                            DescribeProvenance.RepoDerived(),
                            BlockSequence.Create([paragraph])
                        ),
                    ])),
            ]));

        var report = LeanReportFixture.ForDocuments([document]);
        var text = Encoding.UTF8.GetString(CanonicalMarkdownWriter.Write(document, report).AsSpan());

        Assert.Equal(
            "# Sample\n\n"
            + "## Abstract\n\n"
            + "The real embedding is injective.\n\n"
            + "Map $\\varphi$ mirrors `D5/B/S1/Scale/Embedding`.\n\n"
            + "$$\n\\varphi^{2} = \\varphi + 1\n$$\n\n"
            + "## Results\n\n"
            + "<a id=\"describe-formula\"></a>\n\n"
            + "**Example 1.1 (Formula).**\n\n"
            + "$$\n\\varphi^{2} = \\varphi + 1\n$$\n\n"
            + "*Source.* Repository-derived.\n\n"
            + "*Commentary.*\n\n"
            + "Map $\\varphi$ mirrors `D5/B/S1/Scale/Embedding`.\n\n"
            + "<a id=\"describe-injectivity\"></a>\n\n"
            + "**Theorem 1.2 (Injectivity).**\n\n"
            + "$\\operatorname{embed}\\left(x\\right) = 0 \\Rightarrow x = 0$\n\n"
            + "*Proof.* Machine-checked in Lean as "
            + "`D5/S1/Scale/Embedding.embedding_injective` (`✓ std3`). ∎\n\n"
            + "*Source.* Repository-derived.\n\n"
            + "*Commentary.*\n\n"
            + "Map $\\varphi$ mirrors `D5/B/S1/Scale/Embedding`.\n\n"
            + "## References\n\n"
            + "- Truth anchor: `D5/S1/Scale/Embedding.embedding_injective`\n",
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
    public void LiteratureProvenanceEmitsAnAuthorYearDoiCitationFromTypedMetadata()
    {
        var reference = LibraryNoteRef.Create("D5/L/sos1957threegap");
        var document = ScribeDocument.Create(
            CreateHeader(),
            Heading.Create("Literature sample"),
            BlockSequence.Create(
            [
                DocumentBlock.Describe.Remark(
                    DescribeId.Create("three-gap-context"),
                    Heading.Create("Three-gap context"),
                    DescribeStatement.FromFormula(new Formula.Phi()),
                    DescribeProvenance.LiteratureAttested(reference),
                    BlockSequence.Create(
                    [
                        Paragraph(new Inline.Text(TextRun.Create("Referenced context."))),
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
        var text = Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(document, citations: citations).AsSpan());

        Assert.Contains(
            "*Citation.* Vera T. Sos (1957). *On the three gap theorem*. "
            + "DOI: [10.1007/BF01389053](https://doi.org/10.1007/BF01389053).",
            text,
            StringComparison.Ordinal);
        Assert.DoesNotContain("D5/L/sos1957threegap", text, StringComparison.Ordinal);
        Assert.DoesNotContain("lit/sos1957threegap", text, StringComparison.Ordinal);
    }

    [Fact]
    public void LeanDescribeStatementPinsCanonicalTypedFormulaRendering()
    {
        const string latex = "$\\operatorname{Re}\\left(s\\right) = \\frac{1}{2}$";
        var document = ScribeDocument.Create(
            CreateHeader(),
            Heading.Create("Critical line"),
            BlockSequence.Create(
            [
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("critical-line"),
                    Heading.Create("Critical line"),
                    LeanDeclarationRef.Create(
                        "D5/S1/Scale/Embedding.embedding_injective"),
                    CriticalLineFormula(),
                    DescribeProvenance.RepoDerived(),
                    BlockSequence.Create([Paragraph(new Inline.Text(TextRun.Create("Commentary.")))])
                ),
            ]));

        var report = LeanReportFixture.ForDocuments([document]);
        var text = Encoding.UTF8.GetString(CanonicalMarkdownWriter.Write(document, report).AsSpan());

        Assert.Contains("**Theorem 1.1 (Critical line).**\n\n" + latex + "\n\n", text, StringComparison.Ordinal);
        Assert.Contains(
            "*Proof.* Machine-checked in Lean as "
            + "`D5/S1/Scale/Embedding.embedding_injective` (`✓ std3`). ∎",
            text,
            StringComparison.Ordinal);
    }

    private static Formula EmbedInjectiveFormula() => new Formula.Layout(
        FormulaLayoutMode.Inline,
        new Formula.Logic(
            new Formula.Relation(
                new Formula.FunctionCall(
                    FormulaIdentifier.Create("embed"),
                    [new Formula.Symbol(FormulaIdentifier.Create("x"))]),
                FormulaRelationOperator.Equal,
                new Formula.Number(0)),
            FormulaLogicOperator.Implies,
            new Formula.Relation(
                new Formula.Symbol(FormulaIdentifier.Create("x")),
                FormulaRelationOperator.Equal,
                new Formula.Number(0))));

    private static Formula CriticalLineFormula() => new Formula.Layout(
        FormulaLayoutMode.Inline,
        new Formula.Relation(
            new Formula.FunctionCall(
                FormulaIdentifier.Create("Re"),
                [new Formula.Symbol(FormulaIdentifier.Create("s"))]),
            FormulaRelationOperator.Equal,
            new Formula.Fraction(new Formula.Number(1), new Formula.Number(2))));

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
