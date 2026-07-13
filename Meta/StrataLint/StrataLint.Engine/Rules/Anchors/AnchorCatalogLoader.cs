using System.Collections.Immutable;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record AnchorCatalogDefinition(
    string Anchor,
    string? CaseId,
    string? ExpectedSha256,
    string? OpenReason,
    string SourceId,
    string SourcePath,
    string SourceRevision,
    string Status,
    string StructuralSelector,
    string TargetKey,
    string TargetKind);

internal readonly record struct AnchorCatalogStructuralSelector(
    string? HeadingPrefix,
    string LinePrefix,
    string? RequiredToken);

internal sealed class AnchorCatalog
{
    internal AnchorCatalog(ImmutableDictionary<string, AnchorCatalogDefinition> definitions) =>
        Definitions = definitions;

    internal ImmutableDictionary<string, AnchorCatalogDefinition> Definitions { get; }
}

internal static class AnchorCatalogLoader
{
    internal const string RelativePath = "Meta/StrataLint/Generated/anchor-catalog.v1.json";

    private static readonly Regex Sha256Pattern = new(
        "^[0-9a-f]{64}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex CasePattern = new(
        "^D5-T[0-9]{4}$",
        RegexOptions.CultureInvariant);

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
        var targetKeys = new HashSet<string>(StringComparer.Ordinal);
        string? previous = null;
        foreach (var element in array.EnumerateArray())
        {
            var expectedKeys = new[]
            {
                "anchor",
                "case_id",
                "expected_sha256",
                "open_reason",
                "source_id",
                "source_path",
                "source_revision",
                "status",
                "structural_selector",
                "target_key",
                "target_kind",
            };
            if (element.ValueKind != JsonValueKind.Object
                || !PropertyNames(element).SequenceEqual(expectedKeys, StringComparer.Ordinal))
            {
                throw new FormatException("Anchor catalog definition schema is invalid.");
            }

            var anchor = RequiredString(element, "anchor");
            var caseId = OptionalString(element, "case_id");
            var expectedSha256 = OptionalString(element, "expected_sha256");
            var openReason = OptionalString(element, "open_reason");
            var sourceId = RequiredString(element, "source_id");
            var sourcePath = RequiredString(element, "source_path");
            var sourceRevision = RequiredString(element, "source_revision");
            var status = RequiredString(element, "status");
            var selector = RequiredString(element, "structural_selector");
            var targetKey = RequiredString(element, "target_key");
            var targetKind = RequiredString(element, "target_kind");
            if (previous is not null
                && string.CompareOrdinal(previous, anchor) >= 0
                || !RepoPath.TryCreate(sourcePath, out _)
                || targetKind is not ("theory-node" or "spec-clause" or "library-entry" or "mathlib-symbol")
                || !TryParseStructuralSelector(selector, out _)
                || expectedSha256 is not null && !Sha256Pattern.IsMatch(expectedSha256)
                || status is "resolved"
                    && (expectedSha256 is null || caseId is not null || openReason is not null)
                || status is "registered-open"
                    && (caseId is null || openReason is null || !CasePattern.IsMatch(caseId))
                || status is not ("resolved" or "registered-open"))
            {
                throw new FormatException($"Anchor catalog definition is noncanonical: {anchor}.");
            }

            previous = anchor;
            if (!definitions.TryAdd(
                    anchor,
                    new AnchorCatalogDefinition(
                        anchor,
                        caseId,
                        expectedSha256,
                        openReason,
                        sourceId,
                        sourcePath,
                        sourceRevision,
                        status,
                        selector,
                        targetKey,
                        targetKind))
                || !targetKeys.Add(targetKey))
            {
                throw new FormatException("Anchor catalog has a duplicate canonical id or target key.");
            }
        }

        if (definitions.Count == 0)
        {
            throw new FormatException("Anchor catalog has no definitions.");
        }

        return definitions.ToImmutable();
    }

    internal static bool TryParseStructuralSelector(
        string selector,
        out AnchorCatalogStructuralSelector parsed)
    {
        const string headingPrefix = "heading-prefix:";
        const string linePrefix = "line-prefix:";
        const string headingDelimiter = " && line-prefix:";
        const string tokenDelimiter = " && token:";
        parsed = default;

        string? heading = null;
        var linePayload = selector;
        if (selector.StartsWith(headingPrefix, StringComparison.Ordinal))
        {
            var headingEnd = selector.IndexOf(headingDelimiter, StringComparison.Ordinal);
            if (headingEnd <= headingPrefix.Length)
            {
                return false;
            }

            heading = selector[headingPrefix.Length..headingEnd];
            linePayload = selector[(headingEnd + " && ".Length)..];
            if (AtxHeadingLevel(heading) == 0)
            {
                return false;
            }
        }

        if (!linePayload.StartsWith(linePrefix, StringComparison.Ordinal))
        {
            return false;
        }

        var tokenStart = linePayload.IndexOf(tokenDelimiter, StringComparison.Ordinal);
        var line = tokenStart < 0
            ? linePayload[linePrefix.Length..]
            : linePayload[linePrefix.Length..tokenStart];
        var token = tokenStart < 0
            ? null
            : linePayload[(tokenStart + tokenDelimiter.Length)..];
        if (line.Length == 0 || token is "")
        {
            return false;
        }

        parsed = new AnchorCatalogStructuralSelector(heading, line, token);
        return true;
    }

    internal static int AtxHeadingLevel(string line)
    {
        var level = 0;
        while (level < line.Length && level < 6 && line[level] == '#')
        {
            level++;
        }

        return level > 0 && level < line.Length && line[level] == ' ' ? level : 0;
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

    private static string? OptionalString(JsonElement element, string property)
    {
        var value = element.GetProperty(property);
        if (value.ValueKind == JsonValueKind.Null)
        {
            return null;
        }

        return value.ValueKind == JsonValueKind.String && !string.IsNullOrWhiteSpace(value.GetString())
            ? value.GetString()
            : throw new FormatException($"Anchor catalog property {property} must be null or a string.");
    }
}
