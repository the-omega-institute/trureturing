using System.Collections.Immutable;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record CiUnitRegistration(string Id, string Workflow, string? Check);

// This projection reads identity, workflow and check only; ci_units.py owns full admission.
internal static class CiUnitInventory
{
    internal const string RelativePath = "Meta/ci-units.json";
    internal const string UnitCheckSuffix = " / unit";
    private static readonly Regex IdPattern = new("\\A[a-z0-9]+(?:-[a-z0-9]+)*\\z", RegexOptions.CultureInvariant);

    internal static ImmutableArray<CiUnitRegistration> Parse(string text)
    {
        try
        {
            using var document = JsonDocument.Parse(text);
            var root = document.RootElement;
            RequireObject(root);
            if (RequiredString(root, "schema") != "ci-units-v1"
                || !root.TryGetProperty("units", out var units)
                || units.ValueKind != JsonValueKind.Array || units.GetArrayLength() == 0)
                throw new FormatException("CI units require schema ci-units-v1 and a nonempty units array");

            var result = ImmutableArray.CreateBuilder<CiUnitRegistration>();
            var ids = new HashSet<string>(StringComparer.Ordinal);
            var checks = new HashSet<string>(StringComparer.Ordinal);
            foreach (var unit in units.EnumerateArray())
            {
                RequireObject(unit);
                var id = RequiredString(unit, "id");
                var workflow = RequiredString(unit, "workflow");
                if (!IdPattern.IsMatch(id) || !ids.Add(id))
                    throw new FormatException("CI unit id is invalid or duplicated");
                if (!workflow.StartsWith(".github/workflows/", StringComparison.Ordinal)
                    || !workflow.EndsWith(".yml", StringComparison.Ordinal)
                    || workflow.Contains('\\') || workflow.Any(char.IsControl)
                    || workflow.IndexOfAny([':', '*', '?', '[', ']', '!']) >= 0
                    || workflow.Split('/').Any(segment => segment.Length == 0 || segment is "." or ".."))
                    throw new FormatException($"CI unit {id} workflow must be a normalized workflow path");
                if (!unit.TryGetProperty("check", out var check)
                    || check.ValueKind is not (JsonValueKind.Null or JsonValueKind.String))
                    throw new FormatException($"CI unit {id} check must be a string or null");
                var context = check.ValueKind == JsonValueKind.Null ? null : RequiredString(unit, "check");
                if (context is not null && (!checks.Add(context) || context.Any(char.IsControl)))
                    throw new FormatException("CI unit check is invalid or duplicated");
                result.Add(new CiUnitRegistration(id, workflow, context));
            }

            return result.ToImmutable();
        }
        catch (JsonException exception)
        {
            throw new FormatException("CI units registration is invalid JSON", exception);
        }
    }

    private static void RequireObject(JsonElement element)
    {
        if (element.ValueKind != JsonValueKind.Object
            || element.EnumerateObject().Select(property => property.Name).Distinct(StringComparer.Ordinal).Count()
                != element.EnumerateObject().Count())
            throw new FormatException("CI units registration requires objects with unique keys");
    }

    private static string RequiredString(JsonElement element, string key) =>
        element.TryGetProperty(key, out var value) && value.ValueKind == JsonValueKind.String
        && value.GetString() is { Length: > 0 } text && text == text.Trim()
            ? text : throw new FormatException($"CI units {key} must be a nonempty string");
}
