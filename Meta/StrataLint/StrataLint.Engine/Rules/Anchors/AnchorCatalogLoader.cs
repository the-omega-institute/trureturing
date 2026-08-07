using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record AnchorCatalogDefinition(
    string Anchor,
    string Provenance);

internal sealed class AnchorCatalog
{
    internal AnchorCatalog(ImmutableDictionary<string, AnchorCatalogDefinition> definitions) =>
        Definitions = definitions;

    internal ImmutableDictionary<string, AnchorCatalogDefinition> Definitions { get; }
}

internal static class AnchorCatalogLoader
{
    internal const string RelativePath = "Generated/anchor-catalog.v1.json";

    internal static AnchorCatalog Load(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        if (!snapshot.TryGetFile(RelativePath, out var file))
        {
            throw new FormatException("Anchor catalog is missing.");
        }

        using var document = JsonDocument.Parse(file.Text);
        var canonical = StructuredCanonicalWriter.WriteJson(document.RootElement);
        if (!file.RawBytes.AsSpan().SequenceEqual(canonical.AsSpan()))
        {
            throw new FormatException("Anchor catalog bytes are not canonical.");
        }

        var root = document.RootElement;
        if (root.ValueKind != JsonValueKind.Object
            || !PropertyNames(root).SequenceEqual(
                ["definitions", "schema_version"],
                StringComparer.Ordinal)
            || root.GetProperty("schema_version").ValueKind != JsonValueKind.Number
            || root.GetProperty("schema_version").GetInt32() != 1
            || root.GetProperty("definitions").ValueKind != JsonValueKind.Array)
        {
            throw new FormatException("Anchor catalog root schema is invalid.");
        }

        var definitions = ParseDefinitions(root.GetProperty("definitions"));
        return new AnchorCatalog(definitions);
    }

    private static ImmutableDictionary<string, AnchorCatalogDefinition> ParseDefinitions(
        JsonElement array)
    {
        var definitions = ImmutableDictionary.CreateBuilder<string, AnchorCatalogDefinition>(
            StringComparer.Ordinal);
        string? previous = null;
        foreach (var element in array.EnumerateArray())
        {
            var expectedKeys = new[] { "anchor", "provenance" };
            if (element.ValueKind != JsonValueKind.Object
                || !PropertyNames(element).SequenceEqual(expectedKeys, StringComparer.Ordinal))
            {
                throw new FormatException("Anchor catalog definition schema is invalid.");
            }

            var anchor = RequiredString(element, "anchor");
            var provenance = RequiredString(element, "provenance");
            if (previous is not null
                && string.CompareOrdinal(previous, anchor) >= 0
                || provenance.Contains('\r', StringComparison.Ordinal)
                || provenance.Contains('\n', StringComparison.Ordinal))
            {
                throw new FormatException($"Anchor catalog definition is noncanonical: {anchor}.");
            }

            previous = anchor;
            if (!definitions.TryAdd(
                    anchor,
                    new AnchorCatalogDefinition(anchor, provenance)))
            {
                throw new FormatException("Anchor catalog has a duplicate canonical anchor.");
            }
        }

        if (definitions.Count == 0)
        {
            throw new FormatException("Anchor catalog has no definitions.");
        }

        return definitions.ToImmutable();
    }

    private static IEnumerable<string> PropertyNames(JsonElement element) =>
        element.EnumerateObject().Select(static property => property.Name);

    private static string RequiredString(JsonElement element, string property)
    {
        var value = element.GetProperty(property);
        var text = value.ValueKind == JsonValueKind.String ? value.GetString() : null;
        return !string.IsNullOrWhiteSpace(text)
            ? text
            : throw new FormatException($"Anchor catalog property {property} must be a non-empty string.");
    }
}
