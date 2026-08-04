using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class DocumentStructureTests
{
    [Fact]
    public void DocumentAstRepresentsEveryRequiredClosedNodeKind()
    {
        var paragraph = new DocumentBlock.Paragraph(InlineSequence.Create(
        [
            new Inline.Text(TextRun.Create("See ")),
            new Inline.GidReference(GidRef.Create("D5/S1/Scale/Embedding")),
            new Inline.Text(TextRun.Create(" and ")),
            new Inline.InlineFormula(new Formula.Phi()),
            new Inline.Text(TextRun.Create(".")),
        ]));
        var display = new DocumentBlock.DisplayFormula(new Formula.Phi());
        var proposition = DocumentBlock.Describe.Proposition(
            DescribeId.Create("embedding-formula"),
            Heading.Create("Embedding formula"),

                LeanDeclarationRef.Create("D5/S1/Scale/Embedding.embedding_apply"),
            LatexStatement.Create("$\\operatorname{embed}(x) = x$"),
            DescribeProvenance.RepoDerived(),
            BlockSequence.Create([paragraph])
        );
        var theorem = DocumentBlock.Describe.Theorem(
            DescribeId.Create("embedding-is-injective"),
            Heading.Create("Embedding is injective"),

                LeanDeclarationRef.Create("D5/S1/Scale/Embedding.embedding_injective"),
            LatexStatement.Create("$\\operatorname{embed}(x) = 0 \\Rightarrow x = 0$"),
            DescribeProvenance.RepoDerived(),
            BlockSequence.Create([paragraph])
        );
        var section = new DocumentBlock.Section(
            Heading.Create("Consequences"),
            BlockSequence.Create([proposition, theorem]));

        var document = ScribeDocument.Create(
            CreateHeader(),
            Heading.Create("Golden Real Embedding"),
            BlockSequence.Create([paragraph, display, section]));

        Assert.Collection(
            document.Content.Items,
            item => Assert.IsType<DocumentBlock.Paragraph>(item),
            item => Assert.IsType<DocumentBlock.DisplayFormula>(item),
            item => Assert.IsType<DocumentBlock.Section>(item));
        Assert.Collection(
            Assert.IsType<DocumentBlock.Section>(document.Content.Items[2]).Content.Items,
            item => Assert.Equal(
                DescribeKind.Proposition,
                Assert.IsType<DocumentBlock.Describe>(item).Kind),
            item => Assert.Equal(
                DescribeKind.Theorem,
                Assert.IsType<DocumentBlock.Describe>(item).Kind));
    }

    [Fact]
    public void TextRunsAndHeadingsRejectStructuralLineBreaks()
    {
        Assert.Throws<ArgumentException>(() => TextRun.Create("first\nsecond"));
        Assert.Throws<ArgumentException>(() => Heading.Create(" section "));
    }

    [Fact]
    public void ParagraphAndBlockSequencesCannotBeEmpty()
    {
        Assert.Throws<ArgumentException>(() => InlineSequence.Create([]));
        Assert.Throws<ArgumentException>(() => BlockSequence.Create([]));
    }

    private static DocumentHeader CreateHeader() => DocumentHeader.Create(
        GidRef.Create("D5/S1/Scale/Embedding"),
        Generality.Instance,
        GidRef.Create("D5/B/S1/Scale/Embedding"),
        new EvidenceMirror.Waiver(WaiverReason.Create("algebraically-proved")),
        [Anchor.ParseCanonical("mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf")],
        Digest.Create("The real embedding is injective."));
}
