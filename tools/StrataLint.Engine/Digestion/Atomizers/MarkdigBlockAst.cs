using System.Collections.Immutable;
using System.Text.RegularExpressions;
using Markdig;
using Markdig.Extensions.Tables;
using Markdig.Syntax;

namespace StrataLint.Engine;

/// <summary>
/// The block AST behind the default atomizer, parsed by Markdig rather than by the line
/// scanner in <see cref="MarkdownBlockAst"/>. The scanner knows four shapes — ATX heading,
/// fenced code, pipe table, paragraph — and folds everything else into a paragraph, so a
/// volume that states its claims as list items or inside a quote digests as one blob. This
/// reads CommonMark, so those become the blocks they are.
///
/// It replaces the scanner only under <c>generic-v1</c>. The registered dialects keep the
/// scanner because their block boundaries are already baked into content-addressed
/// receipts: a different parser would move the boundaries and invalidate them, which is
/// exactly the thing the frozen ledger does not permit.
///
/// Only leaf blocks are emitted — a heading, a paragraph, a table row — and never the
/// container that holds them. Emitting both would produce overlapping spans, and the
/// atomizer slices the source in one forward pass, so its spans must be disjoint and
/// ordered for the claim slices to reassemble the source byte for byte.
/// </summary>
internal static class MarkdigBlockAst
{
    private static readonly MarkdownPipeline Pipeline = new MarkdownPipelineBuilder()
        .UsePipeTables()
        .UseMathematics()
        .UsePreciseSourceLocation()
        .Build();

    private static readonly Regex AtxHeadingPattern = new(
        "^#{1,6}[ \\t]+(?<text>.*?)[ \\t]*#*[ \\t]*$",
        RegexOptions.CultureInvariant);

    internal static ImmutableArray<MarkdownBlock> Parse(string source)
    {
        ArgumentNullException.ThrowIfNull(source);
        var blocks = ImmutableArray.CreateBuilder<MarkdownBlock>();
        Walk(Markdown.Parse(source, Pipeline), source, LegacyDisplaySpans(source), blocks);
        return blocks.ToImmutable();
    }

    private static void Walk(
        ContainerBlock container,
        string source,
        ImmutableArray<SourceSpan> legacyDisplaySpans,
        ImmutableArray<MarkdownBlock>.Builder blocks)
    {
        foreach (var block in container)
        {
            if (IsInsideLegacyDisplay(block, legacyDisplaySpans))
            {
                continue;
            }

            switch (block)
            {
                case HeadingBlock heading:
                    blocks.Add(new MarkdownHeading(
                        heading.Span.Start,
                        End(heading),
                        heading.Level,
                        HeadingText(Slice(source, heading))));
                    break;

                // A table's rows are its claims, and the delimiter row carries no cell text
                // of its own, which is why it is a header-only row here and skipped there.
                case Table table:
                    foreach (var row in table.OfType<TableRow>())
                    {
                        blocks.Add(Row(source, row));
                    }

                    break;

                // Code is not prose: a claim lead inside a fence or an indented block is a
                // quotation of one, not one. The scanner skips fences for the same reason.
                case CodeBlock:
                case HtmlBlock:
                    break;

                case ParagraphBlock paragraph:
                    blocks.Add(new MarkdownParagraph(
                        paragraph.Span.Start,
                        End(paragraph),
                        Slice(source, paragraph).TrimEnd('\r', '\n')));
                    break;

                case ContainerBlock nested:
                    Walk(nested, source, legacyDisplaySpans, blocks);
                    break;

                default:
                    break;
            }
        }
    }

    /// <summary>
    /// The imported theory volumes also contain a legacy display form delimited by standalone
    /// <c>[</c> and <c>]</c> lines. Markdig cannot name that repository dialect, so an equality
    /// line inside it can otherwise turn the preceding formula lines into a Setext heading.
    /// Paired delimiters make the range structural and keep its contents opaque to claim discovery.
    /// </summary>
    private static ImmutableArray<SourceSpan> LegacyDisplaySpans(string source)
    {
        var spans = ImmutableArray.CreateBuilder<SourceSpan>();
        int? displayStart = null;
        var lineStart = 0;
        while (lineStart < source.Length)
        {
            var lineEnd = source.IndexOfAny(['\r', '\n'], lineStart);
            if (lineEnd < 0)
            {
                lineEnd = source.Length;
            }

            var line = source.AsSpan(lineStart, lineEnd - lineStart).Trim();
            if (displayStart is null && line.SequenceEqual("["))
            {
                displayStart = lineStart;
            }
            else if (displayStart is not null && line.SequenceEqual("]"))
            {
                spans.Add(new SourceSpan(displayStart.Value, lineEnd));
                displayStart = null;
            }

            lineStart = lineEnd;
            while (lineStart < source.Length && source[lineStart] is '\r' or '\n')
            {
                lineStart++;
            }
        }

        return spans.ToImmutable();
    }

    private static bool IsInsideLegacyDisplay(
        MarkdownObject block,
        ImmutableArray<SourceSpan> legacyDisplaySpans)
    {
        var blockStart = block.Span.Start;
        var blockEnd = End(block);
        foreach (var span in legacyDisplaySpans)
        {
            if (span.Start > blockStart)
            {
                return false;
            }

            if (blockStart >= span.Start && blockEnd <= span.End)
            {
                return true;
            }
        }

        return false;
    }

    /// <summary>
    /// Markdig reports a row's span from its first cell's content, past the opening pipe
    /// and the space after it. A row is a line, and the line scanner addresses it as one,
    /// so the start is walked back to the line's own beginning — otherwise the two parsers
    /// would disagree on a shape they both handle, for no reason but a delimiter.
    /// </summary>
    private static MarkdownTableRow Row(string source, TableRow row)
    {
        var start = source.LastIndexOfAny(['\r', '\n'], Math.Max(row.Span.Start - 1, 0)) + 1;
        var text = source[start..Math.Min(End(row), source.Length)].TrimEnd('\r', '\n');
        var firstCellSourceText = MarkdownBlockAst.FirstCellSourceText(text);
        return new MarkdownTableRow(
            start,
            End(row),
            text,
            MarkdownBlockAst.FirstCellPlainText(firstCellSourceText),
            firstCellSourceText,
            row.IsHeader);
    }

    /// <summary>
    /// An ATX heading yields the text between its marks, matching the scanner exactly so
    /// the two agree wherever both can parse. A setext heading has no marks to strip — its
    /// underline is on the following line — so its first line is the text.
    /// </summary>
    private static string HeadingText(string slice)
    {
        var firstLine = slice.AsSpan();
        var lineEnd = firstLine.IndexOfAny('\r', '\n');
        var line = (lineEnd < 0 ? firstLine : firstLine[..lineEnd]).ToString();
        var atx = AtxHeadingPattern.Match(line);
        return atx.Success ? atx.Groups["text"].Value.Trim() : line.Trim();
    }

    /// <summary>
    /// Markdig reports an inclusive end offset; every consumer here wants an exclusive one.
    /// A span is clamped to the source because an empty block reports an empty span whose
    /// end sits one before its start.
    /// </summary>
    private static int End(MarkdownObject block) =>
        Math.Max(block.Span.Start, block.Span.End + 1);

    private static string Slice(string source, MarkdownObject block) =>
        source[block.Span.Start..Math.Min(End(block), source.Length)];

    private sealed record SourceSpan(int Start, int End);
}
