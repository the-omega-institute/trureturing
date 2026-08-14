using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

/// <summary>A claim lead the dialect does not recognise, and the line it was found on.</summary>
internal sealed record UnrecognisedLead(string Cause, int Line);

internal sealed class TheorySourceFormatException(string message) : FormatException(message)
{
    internal static string? IdentifyAt(
        Func<string, string?> identify,
        string value,
        int characterOffset,
        string source,
        List<UnrecognisedLead>? failures = null)
    {
        try
        {
            return identify(value);
        }
        catch (TheorySourceFormatException exception)
        {
            var line = LineNumber(source, characterOffset);
            if (failures is null)
            {
                throw new TheorySourceFormatException($"{exception.Message} at line {line}");
            }

            // One run per unknown lead makes registering a new volume's dialect an
            // O(number of unknown leads) sequence of ingest runs. Collect instead, so the
            // single failure names every lead the source would need registered.
            failures.Add(new UnrecognisedLead(exception.Message, line));
            return null;
        }
    }

    /// <summary>Renders one line per distinct cause, with its first line and occurrence count.</summary>
    internal static string Summarise(IEnumerable<UnrecognisedLead> failures) =>
        string.Join(
            "; ",
            failures
                // Distinct first: a paragraph whose lead is unknown is offered to identify
                // twice, once as its own source line and once as the whole paragraph, and
                // both carry the same line. Counting before that doubles every occurrence.
                .Distinct()
                .GroupBy(static failure => failure.Cause, StringComparer.Ordinal)
                .Select(static group => (Cause: group.Key, Line: group.Min(static item => item.Line), Count: group.Count()))
                .OrderBy(static item => item.Line)
                .Select(static item => item.Count == 1
                    ? $"{item.Cause} at line {item.Line}"
                    : $"{item.Cause} at line {item.Line} ({item.Count} occurrences)"));

    internal static string ClaimLead(string paragraph)
    {
        var start = paragraph.AsSpan().IndexOf("**", StringComparison.Ordinal);
        var end = paragraph.AsSpan(start + 2).IndexOf("**", StringComparison.Ordinal);
        return end < 0
            ? paragraph[start..].TrimEnd()
            : paragraph[start..(start + end + 4)];
    }

    private static int LineNumber(string source, int characterOffset)
    {
        var line = 1;
        for (var index = 0; index < characterOffset; index++)
        {
            if (source[index] == '\n'
                || source[index] == '\r'
                && (index + 1 >= characterOffset || source[index + 1] != '\n'))
            {
                line++;
            }
        }

        return line;
    }
}

internal abstract record MarkdownBlock(int Start, int End);

internal sealed record MarkdownHeading(int Start, int End, int Level, string Text)
    : MarkdownBlock(Start, End);

internal sealed record MarkdownParagraph(int Start, int End, string Text)
    : MarkdownBlock(Start, End);

internal sealed record MarkdownTableRow(
    int Start, int End, string Text, string FirstCellText, string FirstCellSourceText)
    : MarkdownBlock(Start, End);

internal static class MarkdownBlockAst
{
    private static readonly Regex HeadingPattern = new(
        "^(?<marks>#{1,6})[ \\t]+(?<text>.*?)[ \\t]*#*[ \\t]*$",
        RegexOptions.CultureInvariant);
    private static readonly Regex TableDelimiterPattern = new(
        "^[ \\t]*\\|?[ \\t]*:?-{3,}:?[ \\t]*(?:\\|[ \\t]*:?-{3,}:?[ \\t]*)+\\|?[ \\t]*$",
        RegexOptions.CultureInvariant);

    internal static ImmutableArray<MarkdownBlock> Parse(string source)
    {
        var lines = ReadLines(source);
        var blocks = ImmutableArray.CreateBuilder<MarkdownBlock>();
        for (var index = 0; index < lines.Length;)
        {
            var line = lines[index];
            if (string.IsNullOrWhiteSpace(line.Text))
            {
                index++;
                continue;
            }

            var heading = HeadingPattern.Match(line.Text);
            if (heading.Success)
            {
                blocks.Add(new MarkdownHeading(
                    line.Start,
                    line.End,
                    heading.Groups["marks"].Length,
                    heading.Groups["text"].Value.Trim()));
                index++;
                continue;
            }

            if (IsFence(line.Text))
            {
                index = SkipFence(lines, index);
                continue;
            }

            if (index + 1 < lines.Length
                && line.Text.Contains('|')
                && TableDelimiterPattern.IsMatch(lines[index + 1].Text))
            {
                blocks.Add(TableRow(line));
                index += 2;
                while (index < lines.Length
                    && !string.IsNullOrWhiteSpace(lines[index].Text)
                    && lines[index].Text.Contains('|'))
                {
                    blocks.Add(TableRow(lines[index]));
                    index++;
                }

                continue;
            }

            var start = line.Start;
            var contentEnd = line.ContentEnd;
            var end = line.End;
            index++;
            while (index < lines.Length
                && !string.IsNullOrWhiteSpace(lines[index].Text)
                && !HeadingPattern.IsMatch(lines[index].Text)
                && !IsFence(lines[index].Text)
                && !(index + 1 < lines.Length
                    && lines[index].Text.Contains('|')
                    && TableDelimiterPattern.IsMatch(lines[index + 1].Text)))
            {
                contentEnd = lines[index].ContentEnd;
                end = lines[index].End;
                index++;
            }

            blocks.Add(new MarkdownParagraph(start, end, source[start..contentEnd]));
        }

        return blocks.ToImmutable();
    }

    private static MarkdownTableRow TableRow(MarkdownSourceLine line)
    {
        var firstCellSourceText = FirstCellSourceText(line.Text);
        return new(line.Start, line.End, line.Text, FirstCellPlainText(firstCellSourceText), firstCellSourceText);
    }

    internal static string FirstCellSourceText(string row)
    {
        var value = row.Trim();
        if (value.StartsWith('|')) value = value[1..];
        var separator = value.IndexOf('|');
        if (separator >= 0) value = value[..separator];
        return value.Trim();
    }

    internal static string FirstCellPlainText(string value)
    {
        while (value.Length >= 4
            && (value.StartsWith("**", StringComparison.Ordinal)
                && value.EndsWith("**", StringComparison.Ordinal)
                || value.StartsWith("__", StringComparison.Ordinal)
                && value.EndsWith("__", StringComparison.Ordinal)))
        {
            value = value[2..^2].Trim();
        }

        if (value.Length >= 2
            && value.StartsWith('`')
            && value.EndsWith('`'))
        {
            value = value[1..^1].Trim();
        }

        return value;
    }

    private static bool IsFence(string line)
    {
        var trimmed = line.TrimStart();
        return trimmed.StartsWith("```", StringComparison.Ordinal)
            || trimmed.StartsWith("~~~", StringComparison.Ordinal);
    }

    private static int SkipFence(ImmutableArray<MarkdownSourceLine> lines, int start)
    {
        var opening = lines[start].Text.TrimStart();
        var marker = opening.StartsWith("```", StringComparison.Ordinal) ? "```" : "~~~";
        for (var index = start + 1; index < lines.Length; index++)
        {
            if (lines[index].Text.TrimStart().StartsWith(marker, StringComparison.Ordinal))
            {
                return index + 1;
            }
        }

        return lines.Length;
    }

    private static ImmutableArray<MarkdownSourceLine> ReadLines(string source)
    {
        var lines = ImmutableArray.CreateBuilder<MarkdownSourceLine>();
        for (var start = 0; start < source.Length;)
        {
            var contentEnd = start;
            while (contentEnd < source.Length && source[contentEnd] is not ('\r' or '\n'))
            {
                contentEnd++;
            }

            var end = contentEnd;
            if (end < source.Length && source[end] == '\r') end++;
            if (end < source.Length && source[end] == '\n') end++;
            lines.Add(new MarkdownSourceLine(
                start,
                contentEnd,
                end,
                source[start..contentEnd]));
            start = end;
        }

        if (source.Length == 0)
        {
            return [];
        }

        return lines.ToImmutable();
    }

    private sealed record MarkdownSourceLine(int Start, int ContentEnd, int End, string Text);
}
