using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;

namespace StrataLint.Engine;

internal static class StructuredCanonicalWriter
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private static readonly JsonSerializerOptions StringOptions = new()
    {
        Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    internal static ImmutableArray<byte> WriteJson(string text)
    {
        using var document = JsonDocument.Parse(text);
        var builder = new StringBuilder();
        WriteJsonValue(builder, document.RootElement);
        builder.Append('\n');
        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

    internal static ImmutableArray<byte> WriteYaml(string text)
    {
        var value = YamlSubsetParser.Parse(text);
        var builder = new StringBuilder();
        WriteYamlNode(builder, value, 0);
        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

    internal static bool JsonSemanticallyEqual(string left, string right)
    {
        using var leftDocument = JsonDocument.Parse(left);
        using var rightDocument = JsonDocument.Parse(right);
        return JsonElement.DeepEquals(leftDocument.RootElement, rightDocument.RootElement);
    }

    internal static bool YamlSemanticallyEqual(string left, string right)
    {
        var leftElement = JsonSerializer.SerializeToElement(YamlSubsetParser.Parse(left));
        var rightElement = JsonSerializer.SerializeToElement(YamlSubsetParser.Parse(right));
        return JsonElement.DeepEquals(leftElement, rightElement);
    }

    private static void WriteJsonValue(StringBuilder builder, JsonElement element)
    {
        switch (element.ValueKind)
        {
            case JsonValueKind.Object:
                WriteJsonObject(builder, element);
                break;
            case JsonValueKind.Array:
                builder.Append('[');
                var index = 0;
                foreach (var child in element.EnumerateArray())
                {
                    if (index++ > 0) builder.Append(", ");
                    WriteJsonValue(builder, child);
                }

                builder.Append(']');
                break;
            case JsonValueKind.String:
                builder.Append(JsonSerializer.Serialize(element.GetString(), StringOptions));
                break;
            case JsonValueKind.Number:
                builder.Append(CanonicalNumber(element));
                break;
            case JsonValueKind.True:
                builder.Append("true");
                break;
            case JsonValueKind.False:
                builder.Append("false");
                break;
            case JsonValueKind.Null:
                builder.Append("null");
                break;
            default:
                throw new FormatException("JSON contains an unsupported value kind.");
        }
    }

    private static void WriteJsonObject(StringBuilder builder, JsonElement element)
    {
        var properties = element.EnumerateObject().ToArray();
        if (properties.Select(static property => property.Name).Distinct(StringComparer.Ordinal).Count()
            != properties.Length)
        {
            throw new FormatException("JSON object contains duplicate keys.");
        }

        builder.Append('{');
        var index = 0;
        foreach (var property in properties.OrderBy(static property => property.Name, StringComparer.Ordinal))
        {
            if (index++ > 0) builder.Append(", ");
            builder.Append(JsonSerializer.Serialize(property.Name, StringOptions)).Append(": ");
            WriteJsonValue(builder, property.Value);
        }

        builder.Append('}');
    }

    private static string CanonicalNumber(JsonElement element)
    {
        if (!element.TryGetDecimal(out var number))
        {
            throw new FormatException("JSON number is outside the exact canonical decimal domain.");
        }

        if (number == decimal.Zero)
        {
            return "0";
        }

        var text = number.ToString("G29", CultureInfo.InvariantCulture).ToLowerInvariant();
        var exponent = text.IndexOf('e');
        if (exponent < 0)
        {
            return text;
        }

        var mantissa = text[..exponent];
        var exponentText = text[(exponent + 1)..];
        var negative = exponentText.StartsWith("-", StringComparison.Ordinal);
        exponentText = exponentText.TrimStart('+', '-').TrimStart('0');
        if (exponentText.Length == 0) exponentText = "0";
        return $"{mantissa}e{(negative ? "-" : string.Empty)}{exponentText}";
    }

    private static void WriteYamlNode(StringBuilder builder, object? value, int indent)
    {
        if (value is Dictionary<string, object?> mapping)
        {
            if (mapping.Count == 0)
            {
                throw new FormatException("Empty YAML mappings are outside the canonical subset.");
            }

            foreach (var (key, child) in mapping.OrderBy(static pair => pair.Key, StringComparer.Ordinal))
            {
                WriteYamlMappingEntry(builder, key, child, indent);
            }

            return;
        }

        if (value is List<object?> sequence)
        {
            WriteYamlSequence(builder, sequence, indent);
            return;
        }

        throw new FormatException("Canonical YAML root must be a mapping or sequence.");
    }

    private static void WriteYamlMappingEntry(
        StringBuilder builder,
        string key,
        object? value,
        int indent)
    {
        builder.Append(' ', indent).Append(key).Append(':');
        if (IsScalar(value))
        {
            builder.Append(' ').Append(YamlScalar(value)).Append('\n');
        }
        else if (value is List<object?> { Count: 0 })
        {
            builder.Append(" []\n");
        }
        else
        {
            builder.Append('\n');
            WriteYamlNode(builder, value, indent + 2);
        }
    }

    private static void WriteYamlSequence(StringBuilder builder, List<object?> sequence, int indent)
    {
        if (sequence.Count == 0)
        {
            throw new FormatException("An empty YAML sequence needs a mapping key in the canonical subset.");
        }

        foreach (var item in sequence)
        {
            if (IsScalar(item))
            {
                builder.Append(' ', indent).Append("- ").Append(YamlScalar(item)).Append('\n');
                continue;
            }

            if (item is not Dictionary<string, object?> mapping || mapping.Count == 0)
            {
                throw new FormatException("Nested YAML sequences are outside the canonical subset.");
            }

            var entries = mapping.OrderBy(static pair => pair.Key, StringComparer.Ordinal).ToArray();
            var first = entries[0];
            builder.Append(' ', indent).Append("- ").Append(first.Key).Append(':');
            if (IsScalar(first.Value))
            {
                builder.Append(' ').Append(YamlScalar(first.Value)).Append('\n');
            }
            else if (first.Value is List<object?> { Count: 0 })
            {
                builder.Append(" []\n");
            }
            else
            {
                builder.Append('\n');
                WriteYamlNode(builder, first.Value, indent + 4);
            }

            foreach (var (key, child) in entries[1..])
            {
                WriteYamlMappingEntry(builder, key, child, indent + 2);
            }
        }
    }

    private static bool IsScalar(object? value) => value is null or string or int;

    private static string YamlScalar(object? value) => value switch
    {
        null => "null",
        int integer => integer.ToString(CultureInfo.InvariantCulture),
        string text when PlainYamlString(text) => text,
        string text when !text.Contains('"', StringComparison.Ordinal)
            && !text.Contains('\\', StringComparison.Ordinal) => $"\"{text}\"",
        string => throw new FormatException("YAML string needs unsupported escaping."),
        _ => throw new FormatException("YAML scalar type is outside the canonical subset."),
    };

    private static bool PlainYamlString(string value) =>
        value.Length > 0
        && value.Trim() == value
        && value.IndexOfAny(['\r', '\n', '\t', ':', '#']) < 0
        && value is not ("null" or "~" or "[]")
        && !(int.TryParse(value, NumberStyles.None, CultureInfo.InvariantCulture, out var integer)
            && integer >= 0)
        && value[0] is not ('\'' or '"');
}
