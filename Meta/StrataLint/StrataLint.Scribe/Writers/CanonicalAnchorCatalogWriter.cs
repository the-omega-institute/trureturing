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
        var legacy = LegacyAnchorEntries.All
            .OrderBy(static item => item.LegacyValue, StringComparer.Ordinal)
            .Select(static item => new
            {
                canonical = item.CanonicalTargets
                    .Select(static target => target.CanonicalString)
                    .Order(StringComparer.Ordinal)
                    .ToArray(),
                case_id = item.CaseId,
                disposition = DispositionText(item.Disposition),
                evidence = item.Evidence,
                legacy = item.LegacyValue,
            })
            .ToArray();
        var document = JsonSerializer.SerializeToElement(new
        {
            definitions,
            legacy,
            schema_version = 1,
        });
        return StructuredCanonicalWriter.WriteJson(document);
    }

    private static string DispositionText(LegacyAnchorDisposition disposition) => disposition switch
    {
        LegacyAnchorDisposition.Direct => "direct",
        LegacyAnchorDisposition.Alias => "alias",
        LegacyAnchorDisposition.RegisteredOpen => "registered-open",
        LegacyAnchorDisposition.GrandfatheredUnresolved => "grandfathered-unresolved",
        _ => throw new InvalidOperationException("Unknown legacy anchor disposition."),
    };

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

        var registered = definitions
            .Select(static item => item.Anchor.CanonicalString)
            .ToHashSet(StringComparer.Ordinal);
        var legacy = LegacyAnchorEntries.All;
        if (legacy.Select(static item => item.LegacyValue)
                .Distinct(StringComparer.Ordinal).Count() != legacy.Length
            || legacy.Any(item => item.CanonicalTargets.Any(target =>
                !registered.Contains(target.CanonicalString))))
        {
            throw new InvalidOperationException("Legacy anchor table is duplicated or points outside the catalog.");
        }

        var definitionsByAnchor = definitions.ToDictionary(
            static item => item.Anchor.CanonicalString,
            StringComparer.Ordinal);
        foreach (var entry in legacy)
        {
            var targets = entry.CanonicalTargets
                .Select(target => definitionsByAnchor[target.CanonicalString])
                .ToArray();
            if (entry.Disposition is LegacyAnchorDisposition.RegisteredOpen
                ? targets.Any(target =>
                    target.Status is not AnchorRegistrationStatus.RegisteredOpen
                    || !string.Equals(target.CaseId, entry.CaseId, StringComparison.Ordinal))
                : targets.Any(static target =>
                    target.Status is AnchorRegistrationStatus.RegisteredOpen))
            {
                throw new InvalidOperationException(
                    $"Legacy open disposition does not match {entry.LegacyValue} targets.");
            }
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
