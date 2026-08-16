using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class BackfillInventoryLoader
{
    private sealed record ParsedSourceMetadata(
        Dictionary<string, List<string>> Fields,
        bool OmittedGenreRegistryProjection);

    private static ParsedSourceMetadata ParseSourceMetadata(
        string text,
        string path,
        bool allowOmittedGenreRegistryProjection)
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

        var keys = result.Keys.ToHashSet(StringComparer.Ordinal);
        var hasAcknowledgedStale = result.ContainsKey("acknowledged_stale");
        string[] currentKeys = hasAcknowledgedStale
                    ? [
                        "source_id",
                        "path",
                        "atomizer",
                        "genre_registry_check",
                        "unregistered_genres",
                        "acknowledged_stale",
                    ]
                    : [
                        "source_id",
                        "path",
                        "atomizer",
                        "genre_registry_check",
                        "unregistered_genres",
                    ];
        string[] legacyKeys = hasAcknowledgedStale
            ? ["source_id", "path", "atomizer", "acknowledged_stale"]
            : ["source_id", "path", "atomizer"];
        var omittedGenreRegistryProjection = allowOmittedGenreRegistryProjection
            && keys.SetEquals(legacyKeys);
        if (!keys.SetEquals(currentKeys) && !omittedGenreRegistryProjection)
        {
            throw new FormatException($"source metadata keys are not canonical: {path}");
        }


        if (result["source_id"].Count != 1
            || result["path"].Count != 1
            || result["atomizer"].Count != 1
            || string.IsNullOrWhiteSpace(result["source_id"][0])
            || string.IsNullOrWhiteSpace(result["path"][0])
            || string.IsNullOrWhiteSpace(result["atomizer"][0]))
        {
            throw new FormatException(
                $"source metadata identity fields must be single quoted strings: {path}");
        }

        if (omittedGenreRegistryProjection)
        {
            result.Add("genre_registry_check", ["no-registry"]);
            result.Add("unregistered_genres", []);
        }

        return new ParsedSourceMetadata(result, omittedGenreRegistryProjection);
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
