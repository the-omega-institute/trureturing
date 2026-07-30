using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record BlueprintPinManifest(
    ManifestSyntax RouteManifest,
    ImmutableArray<string> Anchors,
    ImmutableArray<string> Imports);

internal abstract record BlueprintPinManifestLoadOutcome
{
    private BlueprintPinManifestLoadOutcome() { }

    internal sealed record Loaded(BlueprintPinManifest Manifest) : BlueprintPinManifestLoadOutcome;

    internal sealed record Rejected(string Message) : BlueprintPinManifestLoadOutcome;
}

internal static class BlueprintPinManifestLoader
{
    private static readonly string[] RequiredKeys =
    {
        "artifact", "anchors", "domain", "generality", "imports", "module", "plane",
        "selector", "tag", "theory",
    };

    internal static BlueprintPinManifestLoadOutcome Load(ReadOnlySpan<byte> bytes)
    {
        try
        {
            var text = new UTF8Encoding(false, true).GetString(bytes);
            using var document = JsonDocument.Parse(text);
            if (document.RootElement.ValueKind != JsonValueKind.Object)
            {
                throw new FormatException("pin manifest JSON must be an object");
            }

            var properties = new Dictionary<string, JsonElement>(StringComparer.Ordinal);
            foreach (var property in document.RootElement.EnumerateObject())
            {
                if (!properties.TryAdd(property.Name, property.Value))
                {
                    throw new FormatException($"pin manifest has a duplicate key: {property.Name}");
                }
            }

            var expected = RequiredKeys.ToHashSet(StringComparer.Ordinal);
            if (properties.Count != expected.Count || properties.Keys.Any(key => !expected.Contains(key)))
            {
                throw new FormatException(
                    "pin manifest keys must be exactly: " + string.Join(", ", RequiredKeys));
            }

            var route = new ManifestSyntax(
                String(properties, "theory"),
                String(properties, "plane"),
                String(properties, "domain"),
                String(properties, "module"),
                String(properties, "generality"),
                String(properties, "selector"),
                String(properties, "artifact"),
                String(properties, "tag"));
            return new BlueprintPinManifestLoadOutcome.Loaded(new BlueprintPinManifest(
                route,
                Strings(properties, "anchors"),
                Strings(properties, "imports")));
        }
        catch (Exception exception) when (exception is DecoderFallbackException or JsonException or FormatException)
        {
            return new BlueprintPinManifestLoadOutcome.Rejected(exception.Message);
        }
    }

    private static string String(IReadOnlyDictionary<string, JsonElement> properties, string name)
    {
        var value = properties[name];
        return value.ValueKind == JsonValueKind.String
            ? value.GetString() ?? string.Empty
            : throw new FormatException($"pin manifest property {name} must be a string");
    }

    private static ImmutableArray<string> Strings(
        IReadOnlyDictionary<string, JsonElement> properties,
        string name)
    {
        var value = properties[name];
        if (value.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException($"pin manifest property {name} must be an array of strings");
        }

        var result = ImmutableArray.CreateBuilder<string>();
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var element in value.EnumerateArray())
        {
            var item = element.ValueKind == JsonValueKind.String ? element.GetString() : null;
            if (string.IsNullOrEmpty(item) || !seen.Add(item))
            {
                throw new FormatException(
                    $"pin manifest property {name} must contain distinct non-empty strings");
            }

            result.Add(item);
        }

        return result.ToImmutable();
    }
}
