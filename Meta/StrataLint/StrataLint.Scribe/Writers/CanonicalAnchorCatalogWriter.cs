using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class CanonicalAnchorCatalogWriter
{
    public const string RelativePath = "Meta/StrataLint/Generated/anchor-catalog.v1.json";

    public static ImmutableArray<byte> Write()
    {
        ValidateDefinitions();
        var definitions = AnchorCatalogDefinitions.All
            .OrderBy(static item => item.Anchor.CanonicalString, StringComparer.Ordinal)
            .Select(static item => new
            {
                anchor = item.Anchor.CanonicalString,
                provenance = item.Provenance,
            })
            .ToArray();
        var document = JsonSerializer.SerializeToElement(new
        {
            definitions,
            schema_version = 1,
        });
        return StructuredCanonicalWriter.WriteJson(document);
    }

    private static void ValidateDefinitions()
    {
        var definitions = AnchorCatalogDefinitions.All;
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
