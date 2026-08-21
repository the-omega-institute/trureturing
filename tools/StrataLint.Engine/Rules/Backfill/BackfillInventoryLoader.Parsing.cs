using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal static partial class BackfillInventoryLoader
{
    private sealed record ParsedSourceMetadata(
        Dictionary<string, List<string>> Fields,
        GenreRegistryProjection GenreRegistryProjection);

    private static ParsedSourceMetadata ParseCandidateSourceMetadata(
        string text,
        string path,
        RawChangeSet? canonicalEncodingChanges = null)
    {
        var fields = ParseSourceMetadataFields(text, path);
        RequireCandidateSourceMetadataKeys(fields, path);
        RequireSourceIdentity(fields, path);
        var check = ParseGenreRegistryCheck(fields, path);
        if (canonicalEncodingChanges is null
            || SourceMetadataWriterInputChanged(fields, path, canonicalEncodingChanges))
        {
            RequireCanonicalSourceMetadata(
                text,
                path,
                BackfillInventoryWriter.WriteSourceMetadata(Source(fields, GenreRegistryProjection.Available(check))));
        }

        return new ParsedSourceMetadata(fields, GenreRegistryProjection.Available(check));
    }

    private static ParsedSourceMetadata ParseBaselineSourceMetadata(
        string text,
        string path)
    {
        var fields = ParseSourceMetadataFields(text, path);
        var keys = fields.Keys.ToHashSet(StringComparer.Ordinal);
        var currentKeys = CandidateSourceMetadataKeys(fields);
        var historicalKeys = HistoricalSourceMetadataKeys(fields);
        if (!keys.SetEquals(currentKeys) && !keys.SetEquals(historicalKeys))
        {
            throw new FormatException($"source metadata keys are not canonical: {path}");
        }

        RequireSourceIdentity(fields, path);
        return new ParsedSourceMetadata(fields, GenreRegistryProjection.Unavailable);
    }

    private static bool SourceMetadataWriterInputChanged(
        IReadOnlyDictionary<string, List<string>> fields,
        string metadataPath,
        RawChangeSet changes)
    {
        var sourceRoot = metadataPath[..^"source.toml".Length];
        var sourcePath = fields["path"].Single();
        return changes.Paths.Any(path =>
            path.Value == metadataPath
            || path.Value == sourcePath
            || path.Value == TheoryAtomizerDataLoader.DataPath
            || path.Value.StartsWith(sourceRoot, StringComparison.Ordinal));
    }

    private static Dictionary<string, List<string>> ParseSourceMetadataFields(
        string text,
        string path)
    {
        var result = new Dictionary<string, List<string>>(StringComparer.Ordinal);
        foreach (var rawLine in text.Split('\n', StringSplitOptions.RemoveEmptyEntries))
        {
            var split = rawLine.Split(" = ", 2, StringSplitOptions.None);
            if (split.Length != 2)
            {
                throw new FormatException($"invalid source metadata: {path}");
            }

            List<string> values;
            try
            {
                values = split[0] == "unregistered_genres"
                    ? ParseTomlBasicStringArray(split[1])
                    : ParseTomlValues(split[1]);
            }
            catch (FormatException) when (split[0] is "source_id" or "path" or "atomizer")
            {
                throw new FormatException(
                    $"source metadata identity fields must be single quoted strings: {path}");
            }

            if (split[0] is "source_id" or "path" or "atomizer"
                && split[1].StartsWith('['))
            {
                throw new FormatException(
                    $"source metadata identity fields must be single quoted strings: {path}");
            }

            if (split[0] == "acknowledged_stale"
                && (!split[1].StartsWith('[')
                    || !split[1].EndsWith(']')
                    || values.Any(string.IsNullOrWhiteSpace)))
            {
                throw new FormatException(
                    $"acknowledged_stale must be a quoted string array without blank elements: {path}");
            }

            if (split[0] == "genre_registry_check" && split[1].StartsWith('['))
            {
                throw new FormatException($"genre_registry_check must be a quoted string: {path}");
            }

            if (split[0] == "unregistered_genres"
                && (!split[1].StartsWith('[') || !split[1].EndsWith(']')))
            {
                throw new FormatException($"unregistered_genres must be a quoted string array: {path}");
            }

            if (!result.TryAdd(split[0], values))
            {
                throw new FormatException($"invalid source metadata: {path}");
            }
        }

        return result;
    }

    private static void RequireCandidateSourceMetadataKeys(
        IReadOnlyDictionary<string, List<string>> fields,
        string path)
    {
        if (!fields.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                CandidateSourceMetadataKeys(fields)))
        {
            throw new FormatException($"source metadata keys are not canonical: {path}");
        }
    }

    private static string[] CandidateSourceMetadataKeys(
        IReadOnlyDictionary<string, List<string>> fields)
    {
        var keys = new List<string>
        {
            "source_id",
            "path",
            "atomizer",
            "genre_registry_check",
            "unregistered_genres",
        };

        if (fields.ContainsKey("acknowledged_stale"))
        {
            keys.Add("acknowledged_stale");
        }

        return [.. keys];
    }

    private static string[] HistoricalSourceMetadataKeys(
        IReadOnlyDictionary<string, List<string>> fields) =>
        fields.ContainsKey("acknowledged_stale")
            ? ["source_id", "path", "atomizer", "acknowledged_stale"]
            : ["source_id", "path", "atomizer"];

    private static void RequireSourceIdentity(
        IReadOnlyDictionary<string, List<string>> fields,
        string path)
    {
        if (fields["source_id"].Count != 1
            || fields["path"].Count != 1
            || fields["atomizer"].Count != 1
            || string.IsNullOrWhiteSpace(fields["source_id"][0])
            || string.IsNullOrWhiteSpace(fields["path"][0])
            || string.IsNullOrWhiteSpace(fields["atomizer"][0]))
        {
            throw new FormatException(
                $"source metadata identity fields must be single quoted strings: {path}");
        }
    }

    private static DigestionLedgerSource Source(
        IReadOnlyDictionary<string, List<string>> fields,
        GenreRegistryProjection projection) =>
        new(
            fields["source_id"].Single(),
            fields["path"].Single(),
            fields["atomizer"].Single(),
            fields.GetValueOrDefault("acknowledged_stale", []).ToImmutableArray(),
            projection,
            []);

    private static void RequireCanonicalSourceMetadata(
        string text,
        string path,
        ImmutableArray<byte> canonical)
    {
        if (!canonical.AsSpan().SequenceEqual(Encoding.UTF8.GetBytes(text)))
        {
            throw new FormatException($"source metadata is not canonically encoded: {path}");
        }
    }

    private static GenreRegistryCheck ParseGenreRegistryCheck(
        IReadOnlyDictionary<string, List<string>> fields,
        string path)
    {
        var names = fields["genre_registry_check"];
        var unregistered = fields["unregistered_genres"].ToImmutableArray();
        if (names.Count != 1)
        {
            throw new FormatException($"genre_registry_check must be a quoted string: {path}");
        }

        if (unregistered.Any(string.IsNullOrWhiteSpace)
            || !unregistered.SequenceEqual(
                unregistered.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal),
                StringComparer.Ordinal))
        {
            throw new FormatException(
                $"unregistered_genres must contain sorted unique nonempty tokens: {path}");
        }

        return names[0] switch
        {
            "collected" => GenreRegistryCheck.Collected(unregistered),
            "no-registry" when unregistered.IsEmpty => GenreRegistryCheck.NoGenreRegistry,
            "no-registry" => throw new FormatException(
                $"no-registry requires empty unregistered_genres: {path}"),
            _ => throw new FormatException($"invalid genre_registry_check: {path}"),
        };
    }

    private static List<string> ParseTomlValues(string encoded)
    {
        if (encoded.StartsWith('[') || encoded.EndsWith(']'))
        {
            if (!encoded.StartsWith('[') || !encoded.EndsWith(']'))
            {
                throw new FormatException("source metadata values must be quoted strings");
            }

            var body = encoded[1..^1];
            if (body.Length == 0) return [];
            return body.Split(", ", StringSplitOptions.None)
                .Select(ParseQuotedTomlScalar)
                .ToList();
        }

        return [ParseQuotedTomlScalar(encoded)];
    }

    private static string ParseQuotedTomlScalar(string encoded)
    {
        if (encoded.Length < 2
            || encoded[0] != '"'
            || encoded[^1] != '"'
            || encoded.AsSpan(1, encoded.Length - 2).Contains('"'))
        {
            throw new FormatException("source metadata values must be quoted strings");
        }

        return encoded[1..^1];
    }

    private static List<string> ParseTomlBasicStringArray(string encoded)
    {
        if (encoded.Length < 2 || encoded[0] != '[' || encoded[^1] != ']')
        {
            throw new FormatException("source metadata values must be quoted strings");
        }

        var values = new List<string>();
        var index = 1;
        var end = encoded.Length - 1;
        while (index < end)
        {
            if (encoded[index++] != '"')
            {
                throw new FormatException("source metadata values must be quoted strings");
            }

            var value = new System.Text.StringBuilder();
            var closed = false;
            while (index < end)
            {
                var character = encoded[index++];
                if (character == '"')
                {
                    closed = true;
                    break;
                }

                if (character == '\\')
                {
                    AppendTomlEscape(encoded, ref index, end, value);
                }
                else if (character < ' ' || character == '\u007f')
                {
                    throw new FormatException("source metadata values must be quoted strings");
                }
                else
                {
                    value.Append(character);
                }
            }

            if (!closed)
            {
                throw new FormatException("source metadata values must be quoted strings");
            }

            values.Add(value.ToString());
            if (index == end)
            {
                break;
            }

            if (index + 1 >= end || encoded[index] != ',' || encoded[index + 1] != ' ')
            {
                throw new FormatException("source metadata values must be quoted strings");
            }

            index += 2;
        }

        return values;
    }

    private static void AppendTomlEscape(
        string encoded,
        ref int index,
        int end,
        System.Text.StringBuilder value)
    {
        if (index >= end)
        {
            throw new FormatException("source metadata values must be quoted strings");
        }

        var escaped = encoded[index++];
        switch (escaped)
        {
            case '"': value.Append('"'); return;
            case '\\': value.Append('\\'); return;
            case 'b': value.Append('\b'); return;
            case 't': value.Append('\t'); return;
            case 'n': value.Append('\n'); return;
            case 'f': value.Append('\f'); return;
            case 'r': value.Append('\r'); return;
            case 'u': value.Append(ReadTomlUnicodeEscape(encoded, ref index, end, 4)); return;
            case 'U': value.Append(ReadTomlUnicodeEscape(encoded, ref index, end, 8)); return;
            default: throw new FormatException("source metadata values must be quoted strings");
        }
    }

    private static string ReadTomlUnicodeEscape(
        string encoded,
        ref int index,
        int end,
        int digits)
    {
        if (index + digits > end
            || !int.TryParse(
                encoded.AsSpan(index, digits),
                System.Globalization.NumberStyles.HexNumber,
                System.Globalization.CultureInfo.InvariantCulture,
                out var scalar)
            || scalar > 0x10ffff
            || scalar is >= 0xd800 and <= 0xdfff)
        {
            throw new FormatException("source metadata values must be quoted strings");
        }

        index += digits;
        return char.ConvertFromUtf32(scalar);
    }

    internal static ImmutableArray<BackfillTicketReference> ParseTickets(string text)
    {
        var tickets = ImmutableArray.CreateBuilder<BackfillTicketReference>();
        foreach (var line in text.Split('\n', StringSplitOptions.RemoveEmptyEntries))
        {
            var parts = line.Split(" = ", 2, StringSplitOptions.None);
            if (parts.Length != 2)
            {
                throw new FormatException("invalid digestion ticket index");
            }

            List<string> values;
            try
            {
                values = ParseTomlValues(parts[1]);
            }
            catch (FormatException)
            {
                throw new FormatException("invalid digestion ticket index");
            }

            if (values.Count != 1)
            {
                throw new FormatException("invalid digestion ticket index");
            }

            tickets.Add(new BackfillTicketReference(parts[0], values[0]));
        }

        return tickets.ToImmutable();
    }
}
