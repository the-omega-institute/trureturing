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
                case_id = item.CaseId,
                expected_sha256 = item.Target.ExpectedSha256,
                open_reason = item.OpenReason,
                source_id = item.Target.SourceId,
                source_path = item.Target.SourcePath,
                source_revision = item.Target.SourceRevision,
                status = item.Status is AnchorRegistrationStatus.Resolved
                    ? "resolved"
                    : "registered-open",
                structural_selector = item.Target.Selector.CanonicalString,
                target_key = item.Target.SemanticKey,
                target_kind = item.Target.TargetKind,
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
                .Distinct(StringComparer.Ordinal).Count() != definitions.Length
            || definitions.Select(static item => item.Target.SemanticKey)
                .Distinct(StringComparer.Ordinal).Count() != definitions.Length)
        {
            throw new InvalidOperationException("Anchor catalog is not a canonical target bijection.");
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
