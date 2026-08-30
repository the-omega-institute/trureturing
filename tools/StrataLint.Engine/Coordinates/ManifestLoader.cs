using System.Text;
using System.Text.Json;
using Trureturing.Truth;

namespace StrataLint.Engine;

public static class ManifestLoader
{
    private static readonly string[] RequiredKeys =
    {
        "artifact", "domain", "generality", "module", "plane", "selector", "tag", "theory",
    };

    private const string OptionalSubdomainKey = "subdomain";

    public static ManifestLoadOutcome Load(ReadOnlySpan<byte> bytes)
    {
        try
        {
            var text = new UTF8Encoding(false, true).GetString(bytes);
            var fields = text.TrimStart().StartsWith('{') ? JsonFields(text) : YamlFields(text);
            var expected = RequiredKeys.ToHashSet(StringComparer.Ordinal);
            if (fields.Keys.Any(key => !expected.Contains(key) && key != OptionalSubdomainKey)
                || expected.Any(key => !fields.ContainsKey(key)))
            {
                throw new FormatException("manifest keys must be exactly: " + string.Join(", ", RequiredKeys));
            }

            var syntax = new ManifestSyntax(
                fields["theory"],
                fields["plane"],
                fields["domain"],
                fields["module"],
                fields["generality"],
                fields["selector"],
                fields["artifact"],
                fields["tag"],
                fields.GetValueOrDefault(OptionalSubdomainKey));
            RouteEngine.ValidateSubDomainApplicability(syntax);
            return new ManifestLoadOutcome.Loaded(syntax);
        }
        catch (Exception exception) when (exception is DecoderFallbackException or JsonException or FormatException)
        {
            return new ManifestLoadOutcome.InfrastructureFailure(exception.Message);
        }
    }

    private static Dictionary<string, string> JsonFields(string text)
    {
        using var document = JsonDocument.Parse(text);
        if (document.RootElement.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException("manifest JSON must be an object");
        }

        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var property in document.RootElement.EnumerateObject())
        {
            if (property.Value.ValueKind != JsonValueKind.String || !result.TryAdd(property.Name, property.Value.GetString() ?? string.Empty))
            {
                throw new FormatException($"manifest has a duplicate key or non-string value: {property.Name}");
            }
        }

        return result;
    }

    private static Dictionary<string, string> YamlFields(string text)
    {
        YamlSubsetSyntaxGuard.RejectUnsupportedSyntax(text, "manifest YAML");
        var mapping = (Dictionary<string, object?>)YamlSubsetParser.Parse(text);

        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var pair in mapping)
        {
            if (pair.Value is not string value || !result.TryAdd(pair.Key, value))
            {
                throw new FormatException("manifest has duplicate/non-scalar keys or a merge key");
            }
        }

        return result;
    }
}

internal static class YamlSubsetSyntaxGuard
{
    internal static void RejectUnsupportedSyntax(string text, string label)
    {
        var lineNumber = 0;
        foreach (var rawLine in text.Split('\n'))
        {
            lineNumber++;
            RejectUnsupportedWhitespace(rawLine, label, lineNumber);
            var line = rawLine.TrimEnd('\r').TrimStart(' ');
            if (line.Length == 0 || line.StartsWith('#'))
            {
                continue;
            }

            if (IsDocumentMarker(line, "---") || IsDocumentMarker(line, "...") || line.StartsWith('%'))
            {
                throw Unsupported(label, lineNumber, "document markers, directives, and multiple documents");
            }

            var node = line.StartsWith("- ", StringComparison.Ordinal)
                ? line[2..].TrimStart()
                : line;
            var separator = node.IndexOf(':');
            if (separator >= 0)
            {
                if (separator + 1 < node.Length && !char.IsWhiteSpace(node[separator + 1]))
                {
                    throw Unsupported(label, lineNumber, "a mapping colon without separating whitespace");
                }

                var key = node[..separator].Trim();
                if (key == "<<")
                {
                    throw Unsupported(label, lineNumber, "a YAML merge key");
                }

                node = node[(separator + 1)..].TrimStart();
            }

            if (node.Length > 0)
            {
                RejectUnsupportedScalar(node, label, lineNumber);
            }
        }
    }

    private static void RejectUnsupportedWhitespace(string line, string label, int lineNumber)
    {
        for (var index = 0; index < line.Length; index++)
        {
            var character = line[index];
            if (character == '\t'
                || character < ' ' && !(character == '\r' && index == line.Length - 1))
            {
                throw Unsupported(label, lineNumber, "tab or control-character indentation");
            }
        }

        if (line.Length > 0 && char.IsWhiteSpace(line[0]) && line[0] is not ' ' and not '\r')
        {
            throw Unsupported(label, lineNumber, "non-space indentation");
        }
    }

    private static void RejectUnsupportedScalar(string scalar, string label, int lineNumber)
    {
        if (scalar == "[]")
        {
            return;
        }

        if (scalar[0] is '\'' or '"')
        {
            var quote = scalar[0];
            if (scalar.Length < 2 || scalar[^1] != quote)
            {
                throw Unsupported(label, lineNumber, "an unterminated or annotated quoted scalar");
            }

            var content = scalar[1..^1];
            if (content.Contains(quote) || quote == '"' && content.Contains('\\'))
            {
                throw Unsupported(label, lineNumber, "quoted-scalar escaping");
            }

            return;
        }

        if (scalar.Contains('#'))
        {
            throw Unsupported(label, lineNumber, "an inline comment");
        }

        var feature = scalar[0] switch
        {
            '&' => "a YAML anchor",
            '*' => "a YAML alias",
            '!' => "a YAML tag",
            '[' or '{' or ']' or '}' => "a flow collection",
            '|' or '>' => "a block scalar",
            ',' or '%' or '@' or '`' => "a reserved scalar indicator",
            _ => null,
        };
        if (feature is not null)
        {
            throw Unsupported(label, lineNumber, feature);
        }

        if (scalar.Length > 1 && scalar[0] == '0' && scalar.All(char.IsAsciiDigit))
        {
            throw Unsupported(label, lineNumber, "a non-canonical integer scalar");
        }
    }

    private static bool IsDocumentMarker(string line, string marker) =>
        line == marker
        || line.StartsWith(marker, StringComparison.Ordinal)
        && line.Length > marker.Length
        && char.IsWhiteSpace(line[marker.Length]);

    private static FormatException Unsupported(string label, int lineNumber, string feature) =>
        new($"{label} uses unsupported {feature} on line {lineNumber}.");
}
