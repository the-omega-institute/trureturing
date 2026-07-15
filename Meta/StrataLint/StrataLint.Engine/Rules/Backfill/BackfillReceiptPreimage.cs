using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal sealed record BackfillReceiptSyntax(
    ImmutableArray<byte> RawBytes,
    ImmutableArray<byte> IdentityBytes);

internal static class BackfillReceiptPreimage
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static ImmutableArray<BackfillReceiptSyntax> Extract(string text)
    {
        ArgumentNullException.ThrowIfNull(text);
        var lines = SplitLines(text);
        var result = ImmutableArray.CreateBuilder<BackfillReceiptSyntax>();
        for (var index = 0; index < lines.Length; index++)
        {
            var entries = lines[index];
            if (!entries.IsContent || !IsMappingHeader(entries, "entries"))
            {
                continue;
            }

            var blockEnd = FindBlockEnd(lines, index + 1, entries.Indent);
            var firstItem = NextContentLine(lines, index + 1, blockEnd);
            if (firstItem < 0)
            {
                index = blockEnd - 1;
                continue;
            }

            var itemIndent = lines[firstItem].Indent;
            if (itemIndent <= entries.Indent || !IsListMappingStart(lines[firstItem]))
            {
                throw new FormatException("BACKFILL entries must contain indented list mappings");
            }

            var starts = Enumerable.Range(firstItem, blockEnd - firstItem)
                .Where(candidate => lines[candidate].IsContent
                    && lines[candidate].Indent == itemIndent
                    && IsListMappingStart(lines[candidate]))
                .ToArray();
            for (var item = 0; item < starts.Length; item++)
            {
                var start = starts[item];
                var end = item + 1 < starts.Length ? starts[item + 1] : blockEnd;
                result.Add(ExtractEntry(lines, start, end, itemIndent));
            }

            index = blockEnd - 1;
        }

        return result.ToImmutable();
    }

    internal static ImmutableArray<byte> RewriteStatus(
        BackfillReceiptSyntax syntax,
        DigestionStatus status)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        ArgumentNullException.ThrowIfNull(status);
        var lines = SplitLines(StrictUtf8.GetString(syntax.RawBytes.AsSpan()));
        if (lines.Length == 0 || !IsListMappingStart(lines[0]))
        {
            throw new FormatException("BACKFILL preserved receipt is not a list mapping");
        }

        var statusLines = FindStatusLines(lines, 0, lines.Length, lines[0].Indent);
        var builder = new StringBuilder();
        for (var index = 0; index < lines.Length; index++)
        {
            if (index == statusLines.Migration)
            {
                builder.Append(RewriteScalar(
                    lines[index].Raw,
                    DigestionStatusNames.Migration(status.Migration)));
            }
            else if (index == statusLines.Truth)
            {
                builder.Append(RewriteScalar(
                    lines[index].Raw,
                    DigestionStatusNames.Truth(status.Truth)));
            }
            else
            {
                builder.Append(lines[index].Raw);
            }
        }

        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

    private static BackfillReceiptSyntax ExtractEntry(
        ImmutableArray<RawLine> lines,
        int start,
        int end,
        int itemIndent)
    {
        var statusLines = FindStatusLines(lines, start, end, itemIndent);
        var raw = new StringBuilder();
        var identity = new StringBuilder();
        for (var index = start; index < end; index++)
        {
            raw.Append(lines[index].Raw);
            if (index != statusLines.Header
                && index != statusLines.Migration
                && index != statusLines.Truth)
            {
                identity.Append(lines[index].Raw);
            }
        }

        return new BackfillReceiptSyntax(
            ImmutableArray.CreateRange(StrictUtf8.GetBytes(raw.ToString())),
            ImmutableArray.CreateRange(StrictUtf8.GetBytes(identity.ToString())));
    }

    private static StatusLines FindStatusLines(
        ImmutableArray<RawLine> lines,
        int start,
        int end,
        int itemIndent)
    {
        var statusHeader = -1;
        var statusIndent = -1;
        if (IsListMappingHeader(lines[start], "status"))
        {
            statusHeader = start;
            statusIndent = itemIndent + 2;
        }

        for (var index = start + 1; index < end; index++)
        {
            if (!lines[index].IsContent
                || lines[index].Indent <= itemIndent
                || !IsMappingHeader(lines[index], "status"))
            {
                continue;
            }

            if (statusHeader >= 0)
            {
                throw new FormatException("BACKFILL entry contains duplicate status mappings");
            }

            statusHeader = index;
            statusIndent = lines[index].Indent;
        }

        if (statusHeader < 0)
        {
            throw new FormatException("BACKFILL entry is missing its status mapping");
        }

        var statusEnd = end;
        for (var index = statusHeader + 1; index < end; index++)
        {
            if (lines[index].IsContent && lines[index].Indent <= statusIndent)
            {
                statusEnd = index;
                break;
            }
        }

        var fieldIndent = -1;
        for (var index = statusHeader + 1; index < statusEnd; index++)
        {
            if (lines[index].IsContent)
            {
                fieldIndent = lines[index].Indent;
                break;
            }
        }

        if (fieldIndent <= statusIndent)
        {
            throw new FormatException("BACKFILL status must be an indented mapping");
        }

        var migration = -1;
        var truth = -1;
        for (var index = statusHeader + 1; index < statusEnd; index++)
        {
            if (!lines[index].IsContent || lines[index].Indent != fieldIndent)
            {
                continue;
            }

            switch (Key(lines[index].Trimmed))
            {
                case "migration" when migration < 0:
                    migration = index;
                    break;
                case "migration":
                    throw new FormatException("BACKFILL status contains duplicate migration fields");
                case "truth" when truth < 0:
                    truth = index;
                    break;
                case "truth":
                    throw new FormatException("BACKFILL status contains duplicate truth fields");
            }
        }

        if (migration < 0 || truth < 0)
        {
            throw new FormatException("BACKFILL status must contain migration and truth fields");
        }

        return new StatusLines(statusHeader, migration, truth);
    }

    private static string Key(string content)
    {
        return YamlSubsetParser.TryParseKeyValue(content, out var key, out _)
            ? key
            : string.Empty;
    }

    private static string RewriteScalar(string raw, string value)
    {
        var newlineLength = raw.EndsWith("\r\n", StringComparison.Ordinal)
            ? 2
            : raw.EndsWith('\n') ? 1 : 0;
        var content = newlineLength == 0 ? raw : raw[..^newlineLength];
        var separator = content.IndexOf(':');
        if (separator < 0)
        {
            throw new FormatException("BACKFILL status field is missing ':'");
        }

        var valueStart = separator + 1;
        while (valueStart < content.Length && char.IsWhiteSpace(content[valueStart]))
        {
            valueStart++;
        }

        var valueEnd = content.Length;
        while (valueEnd > valueStart && char.IsWhiteSpace(content[valueEnd - 1]))
        {
            valueEnd--;
        }

        if (valueStart == valueEnd)
        {
            throw new FormatException("BACKFILL status field must contain a scalar");
        }

        var oldValue = content[valueStart..valueEnd];
        var rendered = oldValue.Length >= 2
            && oldValue[0] == oldValue[^1]
            && oldValue[0] is '\'' or '"'
                ? oldValue[0] + value + oldValue[^1]
                : value;
        return content[..valueStart]
            + rendered
            + content[valueEnd..]
            + raw[^newlineLength..];
    }

    private static bool IsMappingHeader(RawLine line, string expectedKey) =>
        YamlSubsetParser.TryParseKeyValue(line.Trimmed, out var key, out var value)
        && key == expectedKey
        && value is null;

    private static bool IsListMappingHeader(RawLine line, string expectedKey) =>
        line.Trimmed.StartsWith("- ", StringComparison.Ordinal)
        && YamlSubsetParser.TryParseKeyValue(
            line.Trimmed[2..].Trim(),
            out var key,
            out var value)
        && key == expectedKey
        && value is null;

    private static bool IsListMappingStart(RawLine line) =>
        line.Trimmed.StartsWith("- ", StringComparison.Ordinal)
        && YamlSubsetParser.TryParseKeyValue(
            line.Trimmed[2..].Trim(),
            out _,
            out _);

    private static int FindBlockEnd(ImmutableArray<RawLine> lines, int start, int parentIndent)
    {
        for (var index = start; index < lines.Length; index++)
        {
            if (lines[index].IsContent && lines[index].Indent <= parentIndent)
            {
                return index;
            }
        }

        return lines.Length;
    }

    private static int NextContentLine(ImmutableArray<RawLine> lines, int start, int end)
    {
        for (var index = start; index < end; index++)
        {
            if (lines[index].IsContent)
            {
                return index;
            }
        }

        return -1;
    }

    private static ImmutableArray<RawLine> SplitLines(string text)
    {
        var result = ImmutableArray.CreateBuilder<RawLine>();
        var start = 0;
        while (start < text.Length)
        {
            var newline = text.IndexOf('\n', start);
            var end = newline < 0 ? text.Length : newline + 1;
            var raw = text[start..end];
            var content = raw.TrimEnd('\n').TrimEnd('\r');
            var indent = content.Length - content.TrimStart(' ').Length;
            var trimmed = content.Trim();
            result.Add(new RawLine(
                raw,
                indent,
                trimmed,
                trimmed.Length > 0 && !trimmed.StartsWith('#')));
            start = end;
        }

        return result.ToImmutable();
    }

    private sealed record RawLine(string Raw, int Indent, string Trimmed, bool IsContent);

    private sealed record StatusLines(int Header, int Migration, int Truth);
}
