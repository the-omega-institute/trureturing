using System.Collections.Immutable;

namespace StrataLint.Scribe;

/// <summary>One dollar-delimited formula, as a markdown consumer sees it.</summary>
internal readonly record struct MarkdownFormula(bool Display, string Tex, int Line);

/// <summary>
/// Reads the formulas out of rendered markdown the way the site's preprocessor does:
/// paired <c>$</c> or <c>$$</c> delimiters, outside fenced blocks and code spans, with a
/// backslash-escaped delimiter counting as text. Judging the projection rather than the
/// AST is deliberate — the bytes are what the site publishes.
/// </summary>
internal static class MarkdownMath
{
    internal static ImmutableArray<MarkdownFormula> Extract(string markdown)
    {
        ArgumentNullException.ThrowIfNull(markdown);
        var prose = WithoutCode(markdown);
        var formulas = ImmutableArray.CreateBuilder<MarkdownFormula>();
        var index = 0;
        while (index < prose.Length)
        {
            if (prose[index] != '$' || IsEscaped(prose, index))
            {
                index++;
                continue;
            }

            var delimiter = prose.AsSpan(index).StartsWith("$$", StringComparison.Ordinal) ? "$$" : "$";
            var body = index + delimiter.Length;

            // An inline formula never crosses a line; a display formula may.
            var lineEnd = delimiter.Length == 1 ? prose.IndexOf('\n', body) : -1;
            var limit = lineEnd < 0 ? prose.Length : lineEnd;
            var close = Close(prose, body, limit, delimiter);
            if (close < 0)
            {
                index += delimiter.Length;
                continue;
            }

            formulas.Add(new MarkdownFormula(
                delimiter.Length == 2,
                prose[body..close],
                LineOf(prose, index)));
            index = close + delimiter.Length;
        }

        return formulas.ToImmutable();
    }

    private static int Close(string prose, int start, int limit, string delimiter)
    {
        for (var cursor = start; cursor < limit; cursor++)
        {
            if (prose.AsSpan(cursor).StartsWith(delimiter, StringComparison.Ordinal)
                && !IsEscaped(prose, cursor))
            {
                return cursor;
            }
        }

        return -1;
    }

    /// <summary>
    /// The same text with every fenced block and code span blanked to newlines, so line
    /// numbers survive and no delimiter inside code can pair with one outside it.
    /// </summary>
    private static string WithoutCode(string markdown)
    {
        var prose = new System.Text.StringBuilder(markdown.Length);
        string? fence = null;
        var lines = markdown.Split('\n');
        for (var number = 0; number < lines.Length; number++)
        {
            var line = lines[number];
            if (number != 0)
            {
                prose.Append('\n');
            }

            var opener = FenceMarker(line);
            if (fence is null && opener is not null)
            {
                fence = opener;
                continue;
            }

            if (fence is not null)
            {
                if (opener is not null
                    && opener[0] == fence[0]
                    && opener.Length >= fence.Length
                    && line.TrimStart(' ')[opener.Length..].Trim().Length == 0)
                {
                    fence = null;
                }

                continue;
            }

            prose.Append(WithoutCodeSpans(line));
        }

        return prose.ToString();
    }

    /// <summary>The fence marker a line opens or closes with, at most three spaces in.</summary>
    private static string? FenceMarker(string line)
    {
        var indent = line.Length - line.TrimStart(' ').Length;
        if (indent > 3)
        {
            return null;
        }

        var stripped = line.TrimStart(' ');
        var marker = stripped.Length == 0 ? '\0' : stripped[0];
        if (marker is not ('`' or '~'))
        {
            return null;
        }

        var length = 0;
        while (length < stripped.Length && stripped[length] == marker)
        {
            length++;
        }

        return length >= 3 ? stripped[..length] : null;
    }

    private static string WithoutCodeSpans(string line)
    {
        var prose = new System.Text.StringBuilder(line.Length);
        var index = 0;
        while (index < line.Length)
        {
            if (line[index] != '`')
            {
                prose.Append(line[index]);
                index++;
                continue;
            }

            var end = index;
            while (end < line.Length && line[end] == '`')
            {
                end++;
            }

            var span = line[index..end];
            var close = line.IndexOf(span, end, StringComparison.Ordinal);
            if (close < 0)
            {
                // An unclosed run of backticks is literal text, but CommonMark leaves the
                // rest of the line as prose; dropping it would hide formulas from the gate.
                prose.Append(line[index..]);
                break;
            }

            index = close + span.Length;
        }

        return prose.ToString();
    }

    private static bool IsEscaped(string text, int index)
    {
        var backslashes = 0;
        for (var cursor = index - 1; cursor >= 0 && text[cursor] == '\\'; cursor--)
        {
            backslashes++;
        }

        return backslashes % 2 == 1;
    }

    private static int LineOf(string text, int index) =>
        text.AsSpan(0, index).Count('\n') + 1;
}
