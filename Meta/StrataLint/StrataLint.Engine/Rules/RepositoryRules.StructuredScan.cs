using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static bool IsGovernedStructured(RepoPath path, ValidatedPolicy policy) =>
        (RepositoryPathPolicy.TryResolve(path, policy, out _)
            || path.Value == TowerManifestPath)
        && (path.Value.EndsWith(".json", StringComparison.Ordinal)
            || path.Value.EndsWith(".yaml", StringComparison.Ordinal)
            || path.Value.EndsWith(".yml", StringComparison.Ordinal));

    private static void ScanJson(
        string path,
        JsonElement element,
        string location,
        IReadOnlySet<string> tasks,
        ImmutableArray<RuleFinding>.Builder findings,
        bool scanStrings,
        bool enforceKeyOrder)
    {
        if (element.ValueKind == JsonValueKind.Object)
        {
            var properties = element.EnumerateObject().ToArray();
            if (enforceKeyOrder && !properties.Select(static item => item.Name)
                .SequenceEqual(properties.Select(static item => item.Name).Order(StringComparer.Ordinal)))
            {
                findings.Add(new RuleFinding(path, $"object keys are not sorted at {location}"));
                return;
            }

            var classification = ClassifyAnomaly(element);
            if (classification is "unknown")
            {
                findings.Add(new RuleFinding(path, $"unknown anomaly-bearing schema at {location}"));
                return;
            }

            if (classification is "open")
            {
                var caseId = element.TryGetProperty("case_id", out var caseValue)
                    ? caseValue.GetString()
                    : element.TryGetProperty("case", out caseValue) ? caseValue.GetString() : null;
                if (caseId is null || !CasePattern.IsMatch(caseId) || !tasks.Contains(caseId))
                {
                    findings.Add(new RuleFinding(path, $"unledgered anomaly at {location}"));
                }
            }

            foreach (var property in properties)
            {
                if (classification is not null && AnomalySchemaKeys.Contains(property.Name))
                {
                    continue;
                }

                ScanJson(
                    path,
                    property.Value,
                    $"{location}.{property.Name}",
                    tasks,
                    findings,
                    scanStrings,
                    enforceKeyOrder);
            }
        }
        else if (element.ValueKind == JsonValueKind.Array)
        {
            var index = 0;
            foreach (var child in element.EnumerateArray())
            {
                ScanJson(
                    path,
                    child,
                    $"{location}[{index++}]",
                    tasks,
                    findings,
                    scanStrings,
                    enforceKeyOrder);
            }
        }
        else if (scanStrings && element.ValueKind == JsonValueKind.String)
        {
            ScanSerializedString(path, element.GetString() ?? string.Empty, location, tasks, findings);
        }
    }

    private static string? ClassifyAnomaly(JsonElement record)
    {
        if (record.TryGetProperty("kind", out var kindElement) && kindElement.ValueKind == JsonValueKind.String)
        {
            var kind = kindElement.GetString() ?? string.Empty;
            if (AnomalyKindPattern.IsMatch(kind))
            {
                var state = record.TryGetProperty("state", out var stateElement) ? stateElement.GetString() : null;
                return state switch { "resolved" => "closed", "unresolved" => "open", _ => "unknown" };
            }

            if (AnomalyBearingPattern.IsMatch(kind)) return "unknown";
        }

        foreach (var key in new[] { "type", "category", "record_type" })
        {
            if (record.TryGetProperty(key, out var value)
                && value.ValueKind == JsonValueKind.String
                && AnomalyBearingPattern.IsMatch(value.GetString() ?? string.Empty))
            {
                return "unknown";
            }
        }

        if (new[] { "anomalies", "exceptions", "failures", "tensions" }
            .Any(key => record.TryGetProperty(key, out _))) return "unknown";
        if (new[] { "anomaly", "exception", "failure", "tension", "unresolved" }
            .Any(key => record.TryGetProperty(key, out var value) && IsOpen(value))) return "open";
        return null;
    }

    private static bool IsOpen(JsonElement value) => value.ValueKind switch
    {
        JsonValueKind.Null or JsonValueKind.False => false,
        JsonValueKind.String => value.GetString() is not ("" or "none" or "resolved"),
        JsonValueKind.Array => value.GetArrayLength() > 0,
        JsonValueKind.Object => value.EnumerateObject().Any(),
        _ => true,
    };

    private static void ScanSerializedString(
        string path,
        string value,
        string location,
        IReadOnlySet<string> tasks,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        var normalized = value.Replace("\uFEFF", string.Empty, StringComparison.Ordinal).Trim();
        var opaque = new List<string>();
        var cursor = 0;
        var index = 0;
        while (index < normalized.Length)
        {
            if (normalized[index] is not ('{' or '['))
            {
                index++;
                continue;
            }

            if (!TryParseEmbeddedJson(normalized, index, out var document, out var consumed)
                || document is null)
            {
                index++;
                continue;
            }

            using (document)
            {
                opaque.Add(normalized[cursor..index]);
                ScanJson(
                    path,
                    document.RootElement,
                    location,
                    tasks,
                    findings,
                    scanStrings: true,
                    enforceKeyOrder: false);
            }

            cursor = index + consumed;
            index = cursor;
        }

        opaque.Add(normalized[cursor..]);

        var unescaped = Regex.Replace(
            string.Join('\n', opaque),
            "\\\\u([0-9a-fA-F]{4})",
            static match => ((char)Convert.ToInt32(match.Groups[1].Value, 16)).ToString());
        if (AnomalyBearingPattern.IsMatch(unescaped)
            || Regex.IsMatch(unescaped, "\\\"(?:kind|type|category|record_type)\\\"\\s*:"))
        {
            findings.Add(new RuleFinding(path, $"unknown anomaly-bearing schema at {location}"));
        }
    }

    private static bool TryParseEmbeddedJson(
        string value,
        int start,
        out JsonDocument? document,
        out int consumedCharacters)
    {
        var bytes = Encoding.UTF8.GetBytes(value[start..]);
        var reader = new Utf8JsonReader(bytes, isFinalBlock: true, state: default);
        try
        {
            document = JsonDocument.ParseValue(ref reader);
            if (document.RootElement.ValueKind is not (JsonValueKind.Object or JsonValueKind.Array))
            {
                document.Dispose();
                document = null;
                consumedCharacters = 0;
                return false;
            }

            consumedCharacters = Encoding.UTF8.GetCharCount(bytes.AsSpan(0, checked((int)reader.BytesConsumed)));
            return true;
        }
        catch (JsonException)
        {
            document = null;
            consumedCharacters = 0;
            return false;
        }
    }

    private static void ScanYaml(
        string path,
        string text,
        IReadOnlySet<string> tasks,
        ImmutableArray<RuleFinding>.Builder findings,
        bool enforceKeyOrder)
    {
        try
        {
            var value = YamlSubsetParser.Parse(text);
            var element = JsonSerializer.SerializeToElement(value);
            ScanJson(
                path,
                element,
                "$",
                tasks,
                findings,
                scanStrings: true,
                enforceKeyOrder: enforceKeyOrder);
        }
        catch (FormatException exception)
        {
            findings.Add(new RuleFinding(path, $"structured anomaly scan cannot parse YAML: {exception.Message}"));
        }
    }

    private static void ScanLedgerBlocks(
        string path,
        string text,
        IReadOnlySet<string> tasks,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        var matches = Regex.Matches(text, "(?s)<!-- STRATALINT-LEDGER\\n(?<body>.*?)\\n-->");
        var index = 0;
        foreach (Match match in matches)
        {
            index++;
            try
            {
                using var document = JsonDocument.Parse(match.Groups["body"].Value);
                ScanJson(
                    path,
                    document.RootElement,
                    $"ledger block {index}:$",
                    tasks,
                    findings,
                    scanStrings: true,
                    enforceKeyOrder: false);
            }
            catch (JsonException)
            {
                findings.Add(new RuleFinding(path, $"invalid structured ledger block {index}"));
            }
        }
    }
}
