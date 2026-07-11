using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using YamlDotNet.Core;
using YamlDotNet.Core.Events;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Cli;

public static class ManifestLoader
{
    private static readonly string[] RequiredKeys =
    {
        "artifact", "domain", "generality", "module", "plane", "selector", "tag", "theory",
    };

    public static ManifestLoadOutcome Load(ReadOnlySpan<byte> bytes)
    {
        try
        {
            var text = new UTF8Encoding(false, true).GetString(bytes);
            var fields = text.TrimStart().StartsWith('{') ? JsonFields(text) : YamlFields(text);
            var expected = RequiredKeys.ToHashSet(StringComparer.Ordinal);
            if (fields.Count != expected.Count || fields.Keys.Any(key => !expected.Contains(key)))
            {
                throw new FormatException("manifest keys must be exactly: " + string.Join(", ", RequiredKeys));
            }

            return new ManifestLoadOutcome.Loaded(new ManifestSyntax(
                fields["theory"],
                fields["plane"],
                fields["domain"],
                fields["module"],
                fields["generality"],
                fields["selector"],
                fields["artifact"],
                fields["tag"]));
        }
        catch (Exception exception) when (exception is DecoderFallbackException or JsonException or YamlException or FormatException)
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
        var parser = new Parser(new StringReader(text));
        while (parser.MoveNext())
        {
            if (parser.Current is AnchorAlias)
            {
                throw new FormatException("manifest aliases are forbidden");
            }

            if (parser.Current is NodeEvent node
                && (!node.Anchor.IsEmpty || !node.Tag.IsEmpty && !node.Tag.IsNonSpecific))
            {
                throw new FormatException("manifest anchors and custom tags are forbidden");
            }
        }

        var stream = new YamlStream();
        stream.Load(new StringReader(text));
        if (stream.Documents.Count != 1 || stream.Documents[0].RootNode is not YamlMappingNode mapping)
        {
            throw new FormatException("manifest YAML must be one mapping");
        }

        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var pair in mapping.Children)
        {
            if (pair.Key is not YamlScalarNode { Value: not null } key
                || pair.Value is not YamlScalarNode { Value: not null } value
                || key.Value == "<<"
                || !result.TryAdd(key.Value, value.Value))
            {
                throw new FormatException("manifest has duplicate/non-scalar keys or a merge key");
            }
        }

        return result;
    }
}
