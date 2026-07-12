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
        LeanAxiomReport? leanReport = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        var builder = new StringBuilder();
        builder.Append("# ").Append(document.Title.Value).Append("\n\n");
        WriteBlocks(builder, document.Content, 2, leanReport);
        builder.Append('\n');
        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

    private static void WriteBlocks(
        StringBuilder builder,
        BlockSequence content,
        int headingLevel,
        LeanAxiomReport? leanReport)
    {
        for (var index = 0; index < content.Items.Length; index++)
        {
            if (index > 0)
            {
                builder.Append("\n\n");
            }

            WriteBlock(builder, content.Items[index], headingLevel, leanReport);
        }
    }

    private static void WriteBlock(
        StringBuilder builder,
        DocumentBlock block,
        int headingLevel,
        LeanAxiomReport? leanReport)
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
            case DocumentBlock.ComputedValue computed:
                builder.Append("**")
                    .Append(computed.Label.Value)
                    .Append(":** `")
                    .Append(computed.Computation.EvaluateCanonical())
                    .Append("` ")
                    .Append(DeterministicComputation.ProvenanceMarker);
                break;
            case DocumentBlock.RenderedStatement statement:
                WriteRenderedStatement(
                    builder,
                    Resolve(statement.Declaration, leanReport));
                break;
            case DocumentBlock.Section section:
                WriteHeading(builder, headingLevel, section.Title.Value);
                builder.Append("\n\n");
                WriteBlocks(builder, section.Content, headingLevel + 1, leanReport);
                break;
            case DocumentBlock.Proposition proposition:
                WriteStatement(
                    builder,
                    "Proposition",
                    proposition.Title,
                    proposition.Declaration,
                    proposition.Content,
                    headingLevel,
                    leanReport);
                break;
            case DocumentBlock.Theorem theorem:
                WriteStatement(
                    builder,
                    "Theorem",
                    theorem.Title,
                    theorem.Declaration,
                    theorem.Content,
                    headingLevel,
                    leanReport);
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

    private static void WriteStatement(
        StringBuilder builder,
        string kind,
        Heading title,
        LeanDeclarationRef declaration,
        BlockSequence content,
        int headingLevel,
        LeanAxiomReport? leanReport)
    {
        var verified = Resolve(declaration, leanReport);
        WriteHeading(builder, headingLevel, $"{kind}: {title.Value}");
        builder.Append("\n\nLean declaration: `")
            .Append(declaration.Value)
            .Append("` `")
            .Append(verified.AxiomBadge)
            .Append("`\n\n");
        WriteBlocks(builder, content, headingLevel + 1, leanReport);
    }

    private static void WriteRenderedStatement(
        StringBuilder builder,
        VerifiedLeanDeclaration declaration)
    {
        builder.Append("Compiled Lean statement: `")
            .Append(declaration.Reference.Value)
            .Append("` `")
            .Append(declaration.AxiomBadge)
            .Append("`\n\n```text\n")
            .Append(declaration.Declaration.TypeRepresentation)
            .Append("\n```");
    }

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
