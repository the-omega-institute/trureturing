using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static partial class MissionFileLoader
{
    private static ImmutableArray<FrontierEligibilityEntry> ParseFrontierEligibility(
        JsonElement value)
    {
        if (value.ValueKind is not JsonValueKind.Array)
        {
            throw Error(MissionLoadErrorCode.InvalidSchema, "frontier_eligibility must be an array");
        }

        var entries = value.EnumerateArray()
            .Select((item, index) => ParseFrontierEligibilityEntry(item, index))
            .ToImmutableArray();
        if (entries.Select(static entry => entry.SourceRef)
            .Distinct(StringComparer.Ordinal).Count() != entries.Length)
        {
            throw Error(
                MissionLoadErrorCode.InvalidSchema,
                "frontier_eligibility source_ref values must be unique");
        }

        if (!entries.Select(static entry => entry.SourceRef).SequenceEqual(
                entries.Select(static entry => entry.SourceRef).Order(StringComparer.Ordinal),
                StringComparer.Ordinal))
        {
            throw Error(
                MissionLoadErrorCode.InvalidSchema,
                "frontier_eligibility must be ordered by source_ref");
        }

        return entries;
    }

    private static FrontierEligibilityEntry ParseFrontierEligibilityEntry(
        JsonElement value,
        int index)
    {
        var name = $"frontier_eligibility[{index}]";
        var entry = RequireObject(value, MissionLoadErrorCode.InvalidSchema, name);
        var sourceRef = RequireString(entry, "source_ref", MissionLoadErrorCode.InvalidSchema);
        var kindName = RequireString(entry, "kind", MissionLoadErrorCode.InvalidSchema);
        var kind = kindName switch
        {
            "declaration-ready-mathematical-open" =>
                FrontierEligibilityKind.DeclarationReadyMathematicalOpen,
            "mathematical-not-yet-stated" => FrontierEligibilityKind.MathematicalNotYetStated,
            "governance" => FrontierEligibilityKind.Governance,
            "retired" => FrontierEligibilityKind.Retired,
            "unknown" => FrontierEligibilityKind.Unknown,
            _ => throw Error(
                MissionLoadErrorCode.InvalidSchema,
                $"{name}.kind is not a canonical Frontier eligibility kind"),
        };
        if (kind is FrontierEligibilityKind.Retired)
        {
            RequireExactKeys(
                entry,
                ["source_ref", "kind", "delivery_gids"],
                MissionLoadErrorCode.InvalidSchema,
                name);
            return new FrontierEligibilityEntry(
                sourceRef,
                kind,
                ParseCanonicalGidStrings(
                    RequireProperty(entry, "delivery_gids", MissionLoadErrorCode.InvalidSchema),
                    $"{name}.delivery_gids"));
        }

        RequireExactKeys(entry, ["source_ref", "kind"], MissionLoadErrorCode.InvalidSchema, name);
        return new FrontierEligibilityEntry(sourceRef, kind);
    }

    private static ImmutableArray<string> ParseCanonicalGidStrings(
        JsonElement value,
        string name)
    {
        if (value.ValueKind is not JsonValueKind.Array)
        {
            throw Error(MissionLoadErrorCode.InvalidSchema, $"{name} must be an array");
        }

        var values = value.EnumerateArray()
            .Select((item, index) => item.ValueKind is JsonValueKind.String
                && !string.IsNullOrWhiteSpace(item.GetString())
                    ? item.GetString()!
                    : throw Error(
                        MissionLoadErrorCode.InvalidSchema,
                        $"{name}[{index}] must be a non-empty string"))
            .ToImmutableArray();
        if (values.IsDefaultOrEmpty
            || values.Any(static item => !Gid.TryParse(item, out var gid)
                || gid.ToTarget() is not Target.Formal { Declaration: not null }))
        {
            throw Error(
                MissionLoadErrorCode.InvalidSchema,
                $"{name} must contain canonical formal declaration GIDs");
        }

        if (values.Distinct(StringComparer.Ordinal).Count() != values.Length
            || !values.SequenceEqual(values.Order(StringComparer.Ordinal), StringComparer.Ordinal))
        {
            throw Error(
                MissionLoadErrorCode.InvalidSchema,
                $"{name} must be ordered and unique");
        }

        return values;
    }

    private static void ValidateFrontierEligibility(
        RepositorySnapshot snapshot,
        ImmutableArray<FrontierEligibilityEntry> entries)
    {
        foreach (var entry in entries)
        {
            if (!Gid.TryParse(entry.SourceRef, out var gid)
                || !entry.SourceRef.StartsWith("D5/X_Frontier/", StringComparison.Ordinal)
                || gid.Path.Value != entry.SourceRef + ".lean")
            {
                throw Error(
                    MissionLoadErrorCode.InvalidSchema,
                    $"frontier_eligibility source_ref is not a canonical Frontier file GID: {entry.SourceRef}");
            }

            if (!snapshot.TryGetFile(gid.Path.Value, out _)
                && entry.Kind is not FrontierEligibilityKind.Retired)
            {
                throw Error(
                    MissionLoadErrorCode.InvalidSchema,
                    $"frontier_eligibility target is missing: {gid.Path.Value}");
            }

            foreach (var deliveryGid in entry.DeliveryGids.IsDefault
                         ? ImmutableArray<string>.Empty
                         : entry.DeliveryGids)
            {
                if (!Gid.TryParse(deliveryGid, out var delivery)
                    || delivery.ToTarget() is not Target.Formal { Declaration: not null } formal
                    || !snapshot.TryGetFile(formal.Path.Value, out _))
                {
                    throw Error(
                        MissionLoadErrorCode.InvalidSchema,
                        $"frontier_eligibility delivery target is missing or noncanonical: {deliveryGid}");
                }
            }
        }
    }
}
