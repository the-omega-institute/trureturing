using System.Buffers;
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
    private enum AddressSlot
    {
        None,
        Entry,
        HostedExtensions,
        HostedExtension,
        HostedExtensionGid,
        Signature,
        SignatureNameKey,
        SignatureType,
        PrimaryGid,
        CoverageGids,
        CoverageGid,
        Receipts,
        ReceiptList,
        ReceiptEntry,
        ReceiptGid,
    }

    private static bool IsGovernedStructured(RepoPath path, ValidatedPolicy policy) =>
        (RepositoryPathPolicy.TryResolve(path, policy, out _)
            || DigestionFormalizationReceipt.IsCanonicalPath(path.Value)
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

            // canonical receipt 的 precommitted_signature 是封闭的类型化机器记录(kind/name_key/type
            // 各有专属权威校验);其 type 为 statement-v1 编码,天然含定理自身的内容词(如判决枚举
            // 构造子 failure),对象级异常分类在此只会误报——同类判例:a94991935/0d51e2b5f/#3291/#3340。
            var signatureRecordExempt = slot == AddressSlot.Signature
                && DigestionFormalizationReceipt.IsCanonicalPath(path);
            var classification = scanAnomalies && !signatureRecordExempt
                ? ClassifyAnomaly(element)
                : null;
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
                    ArrayElementSlot(slot),
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
        var bytes = Encoding.UTF8.GetBytes(normalized);
        var opaque = new ArrayBufferWriter<byte>(bytes.Length);
        var cursor = 0;
        var index = 0;
        while (index < bytes.Length)
        {
            if (bytes[index] is not ((byte)'{' or (byte)'['))
            {
                index++;
                continue;
            }
            if (!CanStartNonemptyJsonContainer(bytes, index))
            {
                index++;
                continue;
            }

            if (!TryParseEmbeddedJson(bytes, index, out var document, out var consumed)
                || document is null)
            {
                index++;
                continue;
            }

            using (document)
            {
                opaque.Write(bytes.AsSpan(cursor, index - cursor));
                opaque.Write("\n"u8);
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

        opaque.Write(bytes.AsSpan(cursor));

        var unescaped = Regex.Replace(
            Encoding.UTF8.GetString(opaque.WrittenSpan),
            "\\\\u([0-9a-fA-F]{4})",
            static match => ((char)Convert.ToInt32(match.Groups[1].Value, 16)).ToString());
        if ((AnomalyBearingPattern.IsMatch(unescaped)
                && !IsSignatureNameKeyResidueAtDeclaredSlot(path, slot, unescaped)
                && !IsDeclarationGidResidueAtDeclaredSlot(path, slot, unescaped)
                && !IsStatementEncodingResidueAtDeclaredSlot(path, slot, unescaped))
            || Regex.IsMatch(unescaped, "\\\"(?:kind|type|category|record_type)\\\"\\s*:"))
        {
            findings.Add(new RuleFinding(path, $"unknown anomaly-bearing schema at {location}"));
        }
    }

    /// <summary>Advances the structural position by one property name.</summary>
    private static AddressSlot ChildSlot(AddressSlot slot, string name) => (slot, name) switch
    {
        (AddressSlot.Entry, "hosted_extensions") => AddressSlot.HostedExtensions,
        (AddressSlot.Entry, "precommitted_signature") => AddressSlot.Signature,
        (AddressSlot.Entry, "primary_gid") => AddressSlot.PrimaryGid,
        (AddressSlot.Entry, "coverage_gids") => AddressSlot.CoverageGids,
        (AddressSlot.Entry, "receipts") => AddressSlot.Receipts,
        (AddressSlot.Receipts, "coverage") => AddressSlot.ReceiptList,
        (AddressSlot.Receipts, "scribe") => AddressSlot.ReceiptList,
        (AddressSlot.ReceiptEntry, "gid") => AddressSlot.ReceiptGid,
        (AddressSlot.HostedExtension, "precommitted_signature") => AddressSlot.Signature,
        (AddressSlot.HostedExtension, "gid") => AddressSlot.HostedExtensionGid,
        (AddressSlot.Signature, "name_key") => AddressSlot.SignatureNameKey,
        (AddressSlot.Signature, "type") => AddressSlot.SignatureType,
        _ => AddressSlot.None,
    };

    private static AddressSlot ArrayElementSlot(AddressSlot slot) => slot switch
    {
        AddressSlot.HostedExtensions => AddressSlot.HostedExtension,
        AddressSlot.CoverageGids => AddressSlot.CoverageGid,
        AddressSlot.ReceiptList => AddressSlot.ReceiptEntry,
        _ => AddressSlot.None,
    };

    /// <summary>
    /// Tests whether the residue matches the signature-name exemption: the path is a canonical
    /// formalization receipt, structural descent reached a signature's <c>name_key</c>, and the
    /// complete value is a canonical Lean name encoding whose string components have repository
    /// identifier shape. The encoding parser is the Name sub-parser extracted from
    /// <c>StatementV1Decoder</c> and shared back to Scribe; this is not a second grammar. The ASCII
    /// identifier restriction is an additional repository naming policy, not part of Lean's name
    /// encoding grammar.
    ///
    /// No condition is redundant. Without the path, the same signature-shaped keys in arbitrary
    /// governed JSON would be exempt. Without the slot, a root key, a dotted key, or an unrelated
    /// <c>name_key</c> in a receipt would be exempt. Without the shape, prose or JSON anomaly
    /// records placed in the legitimate signature slot would be exempt.
    ///
    /// The slot comes only from structural descent. The rendered location cannot establish it:
    /// property names are rendered without escaping, so a dotted property name and actual nesting
    /// can have the same location text. Embedded-record detection remains a separate disjunct and
    /// is unaffected by this exemption.
    /// </summary>
    private static bool IsSignatureNameKeyResidueAtDeclaredSlot(
        string path,
        AddressSlot slot,
        string residue)
    {
        if (!DigestionFormalizationReceipt.IsCanonicalPath(path)) return false;
        if (slot != AddressSlot.SignatureNameKey) return false;
        if (!CanonicalLeanNameDecoder.IsRepositoryNameKey(residue)) return false;
        return true;
    }

    /// <summary>
    /// Tests whether the residue matches the receipt-GID exemption: the path is a canonical
    /// formalization receipt, structural descent reached the receipt's own <c>primary_gid</c> or
    /// a hosted extension's <c>gid</c>, and the complete value parses under the repository GID
    /// address algebra as selecting a Lean declaration. The shape authority is
    /// <c>DigestionFormalizationReceipt.SelectsDeclaration</c> — the same predicate the canonical
    /// writer enforces — not a second grammar. A GID names its subject, so an anomaly word inside
    /// it (a module or theorem literally about failure) is mathematical content, the same holding
    /// already established for digestion addresses and signature name keys.
    ///
    /// No condition is redundant. Without the path, a <c>primary_gid</c> key in arbitrary governed
    /// JSON would be exempt. Without the slot, a nested or dotted key of the same name would be.
    /// Without the parse, prose or a serialized record placed in the legitimate GID slot would be.
    /// Embedded-record detection remains a separate disjunct and is unaffected.
    /// </summary>
    /// <summary>
    /// Tests whether the residue matches the statement-encoding exemption: the path is a canonical
    /// formalization receipt, structural descent reached a signature's <c>type</c>, and the value
    /// carries the canonical <c>statement-v1(</c> encoding prefix. The prefix is the shape the
    /// producer emits and the receipt loader consumes; like the address exemption, this asserts
    /// the on-record shape rather than a second grammar — a full decode here would duplicate the
    /// Scribe-side StatementV1Decoder for no additional exclusion, since prose placed in this slot
    /// lacks the prefix and stays flagged. Without the path, any <c>type</c> key would be exempt;
    /// without the slot, a nested key would be; without the prefix, anomaly prose in the legitimate
    /// slot would be.
    /// </summary>
    private static bool IsStatementEncodingResidueAtDeclaredSlot(
        string path,
        AddressSlot slot,
        string residue)
    {
        if (!DigestionFormalizationReceipt.IsCanonicalPath(path)) return false;
        if (slot != AddressSlot.SignatureType) return false;
        return residue.StartsWith("statement-v1(", StringComparison.Ordinal);
    }

    private static bool IsDeclarationGidResidueAtDeclaredSlot(
        string path,
        AddressSlot slot,
        string residue)
    {
        var declared = slot switch
        {
            AddressSlot.PrimaryGid or AddressSlot.HostedExtensionGid =>
                DigestionFormalizationReceipt.IsCanonicalPath(path),
            AddressSlot.CoverageGid or AddressSlot.ReceiptGid =>
                BackfillInventoryLoader.IsCanonicalPath(path),
            _ => false,
        };
        return declared && DigestionFormalizationReceipt.SelectsDeclaration(residue);
    }

    private static bool CanStartNonemptyJsonContainer(ReadOnlySpan<byte> value, int start)
    {
        var index = start + 1;
        while (index < value.Length && value[index] is (byte)' ' or (byte)'\t' or (byte)'\r' or (byte)'\n')
        {
            index++;
        }
        if (index >= value.Length || value[index] is (byte)'}' or (byte)']')
        {
            return false;
        }

        if (value[start] == (byte)'{')
        {
            return value[index] == (byte)'"';
        }

        return value[index] is (byte)'"' or (byte)'{' or (byte)'[' or (byte)'-'
            or (byte)'t' or (byte)'f' or (byte)'n'
            || value[index] is >= (byte)'0' and <= (byte)'9';
    }

    private static bool TryParseEmbeddedJson(
        ReadOnlySpan<byte> value,
        int start,
        out JsonDocument? document,
        out int consumedCharacters)
    {
        var reader = new Utf8JsonReader(value[start..], isFinalBlock: true, state: default);
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

            consumedCharacters = checked((int)reader.BytesConsumed);
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

/// <summary>
/// Decodes the canonical Name production emitted by <c>Inspector.encodeName</c>. Scribe uses the
/// prefix entry point inside statement-v1; structured scanning adds full-consumption and repository
/// identifier checks through <see cref="IsRepositoryNameKey"/>.
/// </summary>
internal static class CanonicalLeanNameDecoder
{
    internal static string DecodePrefix(string input, int start, out int consumedCharacters)
    {
        ArgumentNullException.ThrowIfNull(input);
        if ((uint)start > (uint)input.Length) throw new ArgumentOutOfRangeException(nameof(start));

        var parser = new Parser(input, start);
        var decoded = parser.Name(requireRepositoryIdentifier: false);
        consumedCharacters = parser.Position - start;
        return decoded;
    }

    internal static bool IsRepositoryNameKey(string input)
    {
        try
        {
            var parser = new Parser(input, 0);
            _ = parser.Name(requireRepositoryIdentifier: true);
            return parser.Position == input.Length;
        }
        catch (FormatException)
        {
            return false;
        }
    }

    private sealed class Parser(string text, int start)
    {
        internal int Position { get; private set; } = start;

        internal string Name(bool requireRepositoryIdentifier)
        {
            if (TryTake("n0")) return string.Empty;

            var tag = Word(2);
            Take("(");
            var parent = Name(requireRepositoryIdentifier);
            Take(",");
            var part = tag switch
            {
                "ns" => StringPart(requireRepositoryIdentifier),
                "nn" => CanonicalDecimal(),
                _ => throw Error("Unknown name tag."),
            };
            Take(")");
            return parent.Length == 0 ? part : parent + "." + part;
        }

        private string StringPart(bool requireRepositoryIdentifier)
        {
            var value = Atom();
            if (requireRepositoryIdentifier && !IsRepositoryIdentifier(value))
            {
                throw Error("Name component is outside repository identifier policy.");
            }

            return value;
        }

        private string Atom()
        {
            var lengthText = CanonicalDecimal();
            if (!int.TryParse(
                    lengthText,
                    System.Globalization.NumberStyles.None,
                    System.Globalization.CultureInfo.InvariantCulture,
                    out var byteLength))
            {
                throw Error("Atom length exceeds supported input size.");
            }

            Take(":");
            var atomStart = Position;
            var bytes = 0;
            while (bytes < byteLength)
            {
                if (Position == text.Length
                    || Rune.DecodeFromUtf16(
                        text.AsSpan(Position),
                        out var rune,
                        out var consumed) != OperationStatus.Done
                    || bytes + rune.Utf8SequenceLength > byteLength)
                {
                    throw Error("Atom does not match its UTF-8 byte length.");
                }

                Position += consumed;
                bytes += rune.Utf8SequenceLength;
            }

            return text[atomStart..Position];
        }

        private string CanonicalDecimal()
        {
            var start = Position;
            while (Position < text.Length && text[Position] is >= '0' and <= '9') Position++;
            if (start == Position) throw Error("Expected unsigned integer.");
            if (text[start] == '0' && Position - start > 1)
            {
                throw Error("Unsigned integer has leading zeroes.");
            }

            return text[start..Position];
        }

        private string Word(int length)
        {
            if (Position + length > text.Length) throw Error("Unexpected end.");
            var result = text.Substring(Position, length);
            Position += length;
            return result;
        }

        private void Take(string value)
        {
            if (!TryTake(value)) throw Error($"Expected {value}.");
        }

        private bool TryTake(string value)
        {
            if (!text.AsSpan(Position).StartsWith(value, StringComparison.Ordinal)) return false;
            Position += value.Length;
            return true;
        }

        private FormatException Error(string message) => new(
            $"{message} At byte {Encoding.UTF8.GetByteCount(text.AsSpan(0, Position))}.");
    }

    private static bool IsRepositoryIdentifier(string value)
    {
        if (value.Length == 0 || value[0] is not ((>= 'A' and <= 'Z') or (>= 'a' and <= 'z') or '_'))
        {
            return false;
        }

        foreach (var character in value.AsSpan(1))
        {
            if (character is not ((>= 'A' and <= 'Z')
                or (>= 'a' and <= 'z')
                or (>= '0' and <= '9')
                or '_'
                or '\''))
            {
                return false;
            }
        }

        return true;
    }
}
