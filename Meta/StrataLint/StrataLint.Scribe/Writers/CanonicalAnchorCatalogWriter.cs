using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class CanonicalAnchorCatalogWriter
{
    public const string RelativePath = "Meta/StrataLint/Generated/anchor-catalog.v1.json";

    public static ImmutableArray<byte> Write() => Write(AnchorCatalogDefinitions.All);

    internal static ImmutableArray<byte> Write(ImmutableArray<AnchorDefinition> definitions)
    {
        ValidateDefinitions(definitions);
        var projected = definitions
            .OrderBy(static item => item.Anchor.CanonicalString, StringComparer.Ordinal)
            .Select(static item => new
            {
                anchor = item.Anchor.CanonicalString,
                provenance = item.Provenance,
            })
            .ToArray();
        var document = JsonSerializer.SerializeToElement(new
        {
            definitions = projected,
            schema_version = 1,
        });
        return StructuredCanonicalWriter.WriteJson(document);
    }

    private static void ValidateDefinitions(ImmutableArray<AnchorDefinition> definitions)
    {
        if (definitions.Select(static item => item.Anchor.CanonicalString)
                .Distinct(StringComparer.Ordinal).Count() != definitions.Length)
        {
            throw new InvalidOperationException("Anchor catalog does not have unique canonical members.");
        }

        foreach (var definition in definitions)
        {
            if (Anchor.ParseCanonical(definition.Anchor.CanonicalString) != definition.Anchor)
            {
                throw new InvalidOperationException(
                    $"Catalog anchor is not a parser round-trip: {definition.Anchor.CanonicalString}.");
            }
        }
    }
}
