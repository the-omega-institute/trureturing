using System.Collections.Immutable;
using System.Diagnostics;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class CanonicalMarkdownWriter
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static ImmutableArray<byte> Write(
        ScribeDocument document,
        LeanAxiomReport? leanReport = null,
        IReadOnlyDictionary<string, LiteratureCitation>? citations = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        var builder = new StringBuilder();
        builder.Append("# ").Append(document.Title.Value).Append("\n\n");
        builder.Append("## Abstract\n\n")
            .Append(document.Header.Digest.Value)
            .Append("\n\n");
        var describeNumber = 0;
        WriteBlocks(
            builder,
            document.Content,
            2,
            leanReport,
            citations,
            ref describeNumber);
        builder.Append('\n');
        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

    private static void WriteBlocks(
        StringBuilder builder,
        BlockSequence content,
        int headingLevel,
        LeanAxiomReport? leanReport,
        IReadOnlyDictionary<string, LiteratureCitation>? citations,
        ref int describeNumber)
    {
        for (var index = 0; index < content.Items.Length; index++)
        {
            if (index > 0)
            {
                builder.Append("\n\n");
            }

            WriteBlock(
                builder,
                content.Items[index],
                headingLevel,
                leanReport,
                citations,
                ref describeNumber);
        }
    }

    private static void WriteBlock(
        StringBuilder builder,
        DocumentBlock block,
        int headingLevel,
        LeanAxiomReport? leanReport,
        IReadOnlyDictionary<string, LiteratureCitation>? citations,
        ref int describeNumber)
    {
        switch (block)
        {
            case DocumentBlock.Paragraph paragraph:
                WriteParagraph(builder, paragraph.Content);
                break;
            case DocumentBlock.DisplayFormula display:
                builder.Append("$$\n")
                    .Append(LatexWriter.Write(display.Value))
                    .Append("\n$$");
                break;
            case DocumentBlock.Section section:
                WriteHeading(builder, headingLevel, section.Title.Value);
                builder.Append("\n\n");
                WriteBlocks(
                    builder,
                    section.Content,
                    headingLevel + 1,
                    leanReport,
                    citations,
                    ref describeNumber);
                break;
            case DocumentBlock.Describe describe:
                WriteDescribe(
                    builder,
                    describe,
                    headingLevel,
                    leanReport,
                    citations,
                    ref describeNumber);
                break;
            default:
                throw new UnreachableException("Unknown document block.");
        }
    }

    private static void WriteParagraph(StringBuilder builder, InlineSequence content)
    {
        foreach (var inline in content.Items)
        {
            switch (inline)
            {
                case Inline.Text text:
                    builder.Append(text.Run.Value);
                    break;
                case Inline.InlineFormula formula:
                    builder.Append('$')
                        .Append(LatexWriter.Write(formula.Value))
                        .Append('$');
                    break;
                case Inline.GidReference reference:
                    builder.Append('`').Append(reference.Reference.Value).Append('`');
                    break;
                default:
                    throw new UnreachableException("Unknown inline node.");
            }
        }
    }

    private static void WriteDescribe(
        StringBuilder builder,
        DocumentBlock.Describe describe,
        int headingLevel,
        LeanAxiomReport? leanReport,
        IReadOnlyDictionary<string, LiteratureCitation>? citations,
        ref int describeNumber)
    {
        describeNumber++;
        builder.Append("**")
            .Append(DescribeVocabulary.HeadingName(describe.Kind))
            .Append(" 1.")
            .Append(describeNumber)
            .Append(" (")
            .Append(describe.Title.Value)
            .Append(").**");
        switch (describe.Statement)
        {
            case DescribeStatement.FormulaAst formula:
                builder.Append("\n\n$$\n")
                    .Append(LatexWriter.Write(formula.Value))
                    .Append("\n$$");
                break;
            case DescribeStatement.LeanDeclaration lean:
                var verified = Resolve(lean.Value, leanReport);
                if (describe.StatementFormula is { } statementFormula)
                {
                    builder.Append("\n\n")
                        .Append(LatexWriter.WriteStatement(statementFormula));
                }
                else
                {
                    builder.Append("\n\nLean statement: `")
                        .Append(lean.Value.Value)
                        .Append('`');
                }

                if (IsTheoremClass(describe.Kind))
                {
                    builder.Append("\n\n*Proof.* Machine-checked in Lean as `")
                        .Append(lean.Value.Value)
                        .Append("` (`")
                        .Append(verified.AxiomBadge)
                        .Append("`). ∎");
                }
                else
                {
                    builder.Append("\n\n*Formalization.* `")
                        .Append(lean.Value.Value)
                        .Append("` (`")
                        .Append(verified.AxiomBadge)
                        .Append("`).");
                }
                break;
            default:
                throw new UnreachableException("Unknown Describe statement.");
        }

        if (describe.Provenance.LiteratureReference is { } literature)
        {
            if (citations is null
                || !citations.TryGetValue(literature.BibKey.Value, out var citation))
            {
                throw new InvalidOperationException(
                    $"Academic citation is unavailable for {literature.Value}.");
            }

            builder.Append("\n\n*Citation.* ")
                .Append(citation.Authors)
                .Append(" (")
                .Append(citation.Year)
                .Append("). *")
                .Append(citation.Title)
                .Append("*. DOI: [")
                .Append(citation.Doi.Value)
                .Append("](https://doi.org/")
                .Append(citation.Doi.Value)
                .Append(").");
        }
        else
        {
            builder.Append("\n\n*Source.* ");
            builder.Append(DescribeVocabulary.CanonicalName(describe.Provenance.Kind) switch
            {
                "repo-derived" => "Repository-derived.",
                "suspected-novel" => "Suspected novel.",
                "unassessed" => "Unassessed.",
                var provenance => provenance + ".",
            });
        }

        builder.Append("\n\n*Commentary.*\n\n");
        WriteBlocks(
            builder,
            describe.Content,
            headingLevel + 1,
            leanReport,
            citations,
            ref describeNumber);
    }

    private static bool IsTheoremClass(DescribeKind kind) =>
        kind is DescribeKind.Theorem or DescribeKind.Proposition or DescribeKind.Lemma;

    private static VerifiedLeanDeclaration Resolve(
        LeanDeclarationRef declaration,
        LeanAxiomReport? leanReport) =>
        LeanReferenceResolver.Resolve(
            declaration,
            leanReport ?? throw new InvalidOperationException(
                $"Lean compiled-artifact report is required for {declaration.Value}."));

    private static void WriteHeading(
        StringBuilder builder,
        int headingLevel,
        string title)
    {
        if (headingLevel is < 2 or > 6)
        {
            throw new InvalidOperationException("Markdown heading depth exceeds level six.");
        }

        builder.Append('#', headingLevel).Append(' ').Append(title);
    }
}
