using System.Collections.Immutable;
using System.Diagnostics;
using System.Text;

namespace StrataLint.Scribe;

public static class CanonicalMarkdownWriter
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static ImmutableArray<byte> Write(ScribeDocument document)
    {
        ArgumentNullException.ThrowIfNull(document);
        var builder = new StringBuilder();
        builder.Append("# ").Append(document.Title.Value).Append("\n\n");
        WriteBlocks(builder, document.Content, 2);
        builder.Append('\n');
        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

    private static void WriteBlocks(
        StringBuilder builder,
        BlockSequence content,
        int headingLevel)
    {
        for (var index = 0; index < content.Items.Length; index++)
        {
            if (index > 0)
            {
                builder.Append("\n\n");
            }

            WriteBlock(builder, content.Items[index], headingLevel);
        }
    }

    private static void WriteBlock(
        StringBuilder builder,
        DocumentBlock block,
        int headingLevel)
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
                WriteBlocks(builder, section.Content, headingLevel + 1);
                break;
            case DocumentBlock.Proposition proposition:
                WriteStatement(
                    builder,
                    "Proposition",
                    proposition.Title,
                    proposition.Declaration,
                    proposition.Content,
                    headingLevel);
                break;
            case DocumentBlock.Theorem theorem:
                WriteStatement(
                    builder,
                    "Theorem",
                    theorem.Title,
                    theorem.Declaration,
                    theorem.Content,
                    headingLevel);
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
        int headingLevel)
    {
        WriteHeading(builder, headingLevel, $"{kind}: {title.Value}");
        builder.Append("\n\nLean declaration: `")
            .Append(declaration.Value)
            .Append("`\n\n");
        WriteBlocks(builder, content, headingLevel + 1);
    }

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
