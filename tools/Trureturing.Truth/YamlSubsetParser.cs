using System.Globalization;
using System.Text.Json;

namespace Trureturing.Truth;

public static class YamlSubsetParser
{
    public static object Parse(string text)
    {
        var lines = text.Split('\n')
            .Select((raw, index) => new Line(
                raw.Length - raw.TrimStart(' ').Length,
                raw.Trim(),
                index + 1,
                raw))
            .Where(static line => line.Content.Length > 0 && !line.Content.StartsWith('#'))
            .ToArray();
        if (lines.Length == 0)
        {
            throw new FormatException("document is empty");
        }

        var (value, index) = ParseNode(lines, 0, lines[0].Indent);
        if (index != lines.Length || value is not Dictionary<string, object?>)
        {
            throw new FormatException("top-level YAML value must be a mapping");
        }

        return value;
    }

    internal static bool TryParseKeyValue(
        string content,
        out string key,
        out string? value)
    {
        ArgumentNullException.ThrowIfNull(content);
        var separator = content.IndexOf(':');
        if (separator < 0)
        {
            key = string.Empty;
            value = null;
            return false;
        }

        key = content[..separator].Trim();
        if (key.Length == 0
            || !(char.IsAsciiLetter(key[0]) || key[0] == '_')
            || key.Skip(1).Any(static character =>
                !(char.IsAsciiLetterOrDigit(character) || character is '_' or '.' or '-')))
        {
            key = string.Empty;
            value = null;
            return false;
        }

        var rawValue = content[(separator + 1)..].Trim();
        value = rawValue.Length == 0 ? null : rawValue;
        return true;
    }

    private static (object Value, int Index) ParseNode(Line[] lines, int index, int indent)
    {
        if (lines[index].Indent != indent)
        {
            throw new FormatException($"unexpected indentation on line {lines[index].Number}");
        }

        return lines[index].Content.StartsWith("- ", StringComparison.Ordinal)
            ? ParseList(lines, index, indent)
            : ParseMapping(lines, index, indent);
    }

    private static (object Value, int Index) ParseMapping(Line[] lines, int index, int indent)
    {
        var result = new Dictionary<string, object?>(StringComparer.Ordinal);
        while (index < lines.Length
            && lines[index].Indent == indent
            && !lines[index].Content.StartsWith("- ", StringComparison.Ordinal))
        {
            var line = lines[index];
            var (key, rawValue) = KeyValue(line.Content, line.Number);
            if (!result.TryAdd(key, null))
            {
                throw new FormatException($"duplicate key '{key}' on line {line.Number}");
            }

            index++;
            object? value;
            if (rawValue is null)
            {
                if (index >= lines.Length || lines[index].Indent <= indent)
                {
                    value = null;
                }
                else
                {
                    (value, index) = ParseNode(lines, index, lines[index].Indent);
                }
            }
            else if (IsBlockMarker(rawValue))
            {
                (value, index) = ParseBlockScalar(lines, index, indent);
            }
            else if (rawValue == "[]")
            {
                value = new List<object?>();
            }
            else
            {
                value = Scalar(rawValue);
            }

            result[key] = value;
        }

        return (result, index);
    }

    private static (object Value, int Index) ParseList(Line[] lines, int index, int indent)
    {
        var result = new List<object?>();
        while (index < lines.Length
            && lines[index].Indent == indent
            && lines[index].Content.StartsWith("- ", StringComparison.Ordinal))
        {
            var line = lines[index];
            var item = line.Content[2..].Trim();
            index++;
            if (item.Length == 0)
            {
                if (index >= lines.Length || lines[index].Indent <= indent)
                {
                    throw new FormatException($"empty list item on line {line.Number}");
                }

                var parsed = ParseNode(lines, index, lines[index].Indent);
                result.Add(parsed.Value);
                index = parsed.Index;
                continue;
            }

            if (!item.Contains(':', StringComparison.Ordinal))
            {
                result.Add(Scalar(item));
                continue;
            }

            var (key, rawValue) = KeyValue(item, line.Number);
            var mapping = new Dictionary<string, object?>(StringComparer.Ordinal);
            object? value;
            if (rawValue is null)
            {
                if (index >= lines.Length || lines[index].Indent <= indent)
                {
                    value = null;
                }
                else
                {
                    (value, index) = ParseNode(lines, index, lines[index].Indent);
                }
            }
            else if (IsBlockMarker(rawValue))
            {
                (value, index) = ParseBlockScalar(lines, index, indent);
            }
            else
            {
                value = Scalar(rawValue);
            }

            mapping.Add(key, value);
            if (index < lines.Length && lines[index].Indent > indent)
            {
                var parsed = ParseMapping(lines, index, lines[index].Indent);
                var continuation = (Dictionary<string, object?>)parsed.Value;
                foreach (var pair in continuation)
                {
                    if (!mapping.TryAdd(pair.Key, pair.Value))
                    {
                        throw new FormatException($"duplicate list mapping key '{pair.Key}'");
                    }
                }

                index = parsed.Index;
            }

            result.Add(mapping);
        }

        return (result, index);
    }

    private static (object Value, int Index) ParseBlockScalar(Line[] lines, int index, int parentIndent)
    {
        if (index >= lines.Length || lines[index].Indent <= parentIndent)
        {
            return (string.Empty, index);
        }

        var content = new List<string>();
        var contentIndent = lines[index].Indent;
        while (index < lines.Length && lines[index].Indent >= contentIndent)
        {
            content.Add(lines[index].Content);
            index++;
        }

        return (string.Join('\n', content), index);
    }

    private static (string Key, string? Value) KeyValue(string content, int number)
    {
        if (TryParseKeyValue(content, out var key, out var value))
        {
            return (key, value);
        }

        if (!content.Contains(':', StringComparison.Ordinal))
        {
            throw new FormatException($"expected key:value on line {number}");
        }

        throw new FormatException($"invalid key on line {number}");
    }

    private static object? Scalar(string value)
    {
        if (value == "[]") return new List<object?>();
        if (value is "null" or "~") return null;
        if (int.TryParse(
                value,
                NumberStyles.Integer,
                CultureInfo.InvariantCulture,
                out var integer)
            && integer >= 0)
        {
            return integer;
        }
        if (value.Length >= 2 && value[0] == value[^1] && value[0] == '"')
        {
            try
            {
                return JsonSerializer.Deserialize<string>(value)
                    ?? throw new FormatException("double-quoted YAML scalar decoded to null");
            }
            catch (JsonException)
            {
                return value[1..^1];
            }
        }
        if (value.Length >= 2 && value[0] == value[^1] && value[0] == '\'')
        {
            return value[1..^1];
        }
        return value;
    }

    private static bool IsBlockMarker(string value) =>
        value is "|" or "|-" or "|+" or ">" or ">-" or ">+";

    private sealed record Line(int Indent, string Content, int Number, string Raw);
}
