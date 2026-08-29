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
        RejectUnsupportedYamlFeatures(text);
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

    private static void RejectUnsupportedYamlFeatures(string text)
    {
        foreach (var rawLine in text.Split('\n'))
        {
            var line = rawLine.TrimStart();
            if (line.Length == 0 || line.StartsWith('#'))
            {
                continue;
            }

            var separator = line.IndexOf(':');
            var key = separator < 0 ? string.Empty : line[..separator].Trim();
            var value = separator < 0 ? string.Empty : line[(separator + 1)..].TrimStart();
            if (key == "<<")
            {
                throw new FormatException("manifest merge keys are forbidden");
            }

            if (value.StartsWith('&'))
            {
                throw new FormatException("manifest anchors are forbidden");
            }

            if (value.StartsWith('*'))
            {
                throw new FormatException("manifest aliases are forbidden");
            }

            if (value.StartsWith('!'))
            {
                throw new FormatException("manifest custom tags are forbidden");
            }
        }
    }
}
