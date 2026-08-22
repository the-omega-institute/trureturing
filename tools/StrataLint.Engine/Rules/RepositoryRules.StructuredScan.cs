using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    /// <summary>
    /// The candidate structural position of a node, tracked as the scan descends. <c>Entry</c> is
    /// assigned to the root of every scanned document, which is where a digestion entry would sit
    /// if the document were one; the position says where a node stands, not what the document is.
    /// </summary>
    private enum AddressSlot { None, Entry, Boundary, Address }

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
        AddressSlot slot,
        IReadOnlySet<string> tasks,
        ImmutableArray<RuleFinding>.Builder findings,
        bool scanAnomalies,
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

            var classification = scanAnomalies ? ClassifyAnomaly(element) : null;
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
                    ChildSlot(slot, property.Name),
                    tasks,
                    findings,
                    scanAnomalies,
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
                    AddressSlot.None,
                    tasks,
                    findings,
                    scanAnomalies,
                    scanStrings,
                    enforceKeyOrder);
            }
        }
        else if (scanStrings && element.ValueKind == JsonValueKind.String)
        {
            ScanSerializedString(path, element.GetString() ?? string.Empty, location, slot, tasks, findings);
        }
    }

    private static string? ClassifyAnomaly(JsonElement record)
    {
        if (record.TryGetProperty("kind", out var kindElement) && kindElement.ValueKind == JsonValueKind.String)
        {
            var kind = kindElement.GetString() ?? string.Empty;
            if (kind == "revocation-receipt")
            {
                return "closed";
            }

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
        AddressSlot slot,
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
                    AddressSlot.None,
                    tasks,
                    findings,
                    scanAnomalies: true,
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
        if ((AnomalyBearingPattern.IsMatch(unescaped) && !IsAddressShapedResidueAtDeclaredSlot(path, slot, unescaped))
            || Regex.IsMatch(unescaped, "\\\"(?:kind|type|category|record_type)\\\"\\s*:"))
        {
            findings.Add(new RuleFinding(path, $"unknown anomaly-bearing schema at {location}"));
        }
    }

    /// <summary>
    /// Advances the structural position by one property name. Reading the position from the
    /// rendered location would not work: a property name is written there without escaping, so a
    /// key literally called <c>boundary.ast_path</c> and a real nesting of <c>boundary</c> over
    /// <c>ast_path</c> render alike. Only the descent tells them apart.
    /// </summary>
    private static AddressSlot ChildSlot(AddressSlot slot, string name) => (slot, name) switch
    {
        (AddressSlot.Entry, "ast_path") => AddressSlot.Address,
        (AddressSlot.Entry, "boundary") => AddressSlot.Boundary,
        (AddressSlot.Boundary, "ast_path") => AddressSlot.Address,
        _ => AddressSlot.None,
    };

    /// <summary>
    /// Tests whether the residue matches the exemption: the path is one the inventory loader
    /// recognises, the descent reached the address slot, and the value is shaped as an address —
    /// free of whitespace and two or more non-empty segments joined by <c>/</c>. It establishes
    /// those three facts and nothing beyond them; it does not parse the record, and it does not
    /// show that any entry was declared or loaded.
    ///
    /// No condition is redundant. Without the path, a stray key of the same name in any governed
    /// artifact would be exempt. Without the slot, a dotted key and any nesting depth would be.
    /// Without the shape, a prose report written into the address field would be.
    ///
    /// Two limits are worth stating. <c>IsCanonicalPath</c> also recognises a source manifest,
    /// which is TOML and so never reaches this scan, but the predicate does not itself exclude it.
    /// And the shape is what the addresses on record look like rather than a grammar the schema
    /// states, so an adapter that one day emits a single-segment address would meet a false
    /// positive here and this condition would have to follow the schema. The two boundary layouts
    /// are mutually exclusive by the ledger schema, which is checked elsewhere; nothing here
    /// establishes that exclusivity.
    ///
    /// The serialized record test beside this one is a separate disjunct and is unaffected.
    /// </summary>
    private static bool IsAddressShapedResidueAtDeclaredSlot(
        string path,
        AddressSlot slot,
        string residue)
    {
        if (!BackfillInventoryLoader.IsCanonicalPath(path)) return false;
        if (slot != AddressSlot.Address) return false;
        if (residue.Any(char.IsWhiteSpace)) return false;
        var segments = residue.Split('/');
        return segments.Length >= 2 && segments.All(segment => segment.Length > 0);
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
        bool scanAnomalies,
        bool enforceKeyOrder,
        bool reportParseErrors)
    {
        try
        {
            var value = YamlSubsetParser.Parse(text);
            var element = JsonSerializer.SerializeToElement(value);
            ScanJson(
                path,
                element,
                "$",
                AddressSlot.Entry,
                tasks,
                findings,
                scanAnomalies,
                scanStrings: scanAnomalies,
                enforceKeyOrder: enforceKeyOrder);
        }
        catch (FormatException exception)
        {
            if (reportParseErrors)
            {
                findings.Add(new RuleFinding(path, $"structured anomaly scan cannot parse YAML: {exception.Message}"));
            }
        }
    }

    private static void ScanLedgerBlocks(
        string path,
        string text,
        IReadOnlySet<string> tasks,
        ImmutableArray<RuleFinding>.Builder findings,
        bool scanAnomalies,
        bool reportParseErrors)
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
                    AddressSlot.None,
                    tasks,
                    findings,
                    scanAnomalies,
                    scanStrings: scanAnomalies,
                    enforceKeyOrder: false);
            }
            catch (JsonException)
            {
                if (reportParseErrors)
                {
                    findings.Add(new RuleFinding(path, $"invalid structured ledger block {index}"));
                }
            }
        }
    }
}
