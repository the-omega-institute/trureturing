using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;

namespace StrataLint.Engine;

// DTR v1 uses compact, recursively sorted JSON, unlike the spaced report wire format.
internal static class InformationTemplateJson
{
    private static readonly UTF8Encoding Utf8 = new(false, true);

    internal static JsonDocument Read(ReadOnlySpan<byte> bytes)
    {
        try
        {
            var document = JsonDocument.Parse(Utf8.GetString(bytes));
            try
            {
                if (!Canonical(document.RootElement).AsSpan().SequenceEqual(bytes))
                    throw new FormatException("DTR-DebtSchema: noncanonical JSON bytes");
                return document;
            }
            catch
            {
                document.Dispose();
                throw;
            }
        }
        catch (Exception ex) when (ex is JsonException or DecoderFallbackException)
        {
            throw new FormatException("DTR-DebtSchema: invalid JSON/UTF-8", ex);
        }
    }

    internal static ImmutableArray<byte> Canonical(JsonElement value, bool newline = true)
    {
        using var stream = new MemoryStream();
        using (var writer = new Utf8JsonWriter(stream, new JsonWriterOptions
        {
            Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
        }))
        {
            Write(writer, value);
        }

        if (newline) stream.WriteByte((byte)'\n');
        return ImmutableArray.CreateRange(stream.ToArray());
    }

    private static void Write(Utf8JsonWriter writer, JsonElement value)
    {
        switch (value.ValueKind)
        {
            case JsonValueKind.Object:
                var fields = value.EnumerateObject().OrderBy(p => p.Name, StringComparer.Ordinal).ToArray();
                if (fields.Select(p => p.Name).Distinct(StringComparer.Ordinal).Count() != fields.Length)
                    throw new FormatException("DTR-DebtSchema: duplicate JSON member");
                writer.WriteStartObject();
                foreach (var field in fields)
                {
                    writer.WritePropertyName(field.Name);
                    Write(writer, field.Value);
                }

                writer.WriteEndObject();
                break;
            case JsonValueKind.Array:
                writer.WriteStartArray();
                foreach (var item in value.EnumerateArray()) Write(writer, item);
                writer.WriteEndArray();
                break;
            default:
                value.WriteTo(writer);
                break;
        }
    }

    internal static void Fields(JsonElement value, params string[] expected)
    {
        if (value.ValueKind != JsonValueKind.Object
            || !value.EnumerateObject().Select(p => p.Name).Order(StringComparer.Ordinal)
                .SequenceEqual(expected.Order(StringComparer.Ordinal)))
            throw new FormatException("DTR-DebtSchema: missing, duplicate or unknown fields");
    }

    internal static string String(JsonElement value, string field)
    {
        if (!value.TryGetProperty(field, out var item) || item.ValueKind != JsonValueKind.String
            || item.GetString() is not { Length: > 0 } text)
            throw new FormatException($"DTR-DebtSchema: nonempty string required: {field}");
        return text;
    }

    internal static void Version(JsonElement value)
    {
        if (!value.TryGetProperty("schema_version", out var item)
            || item.ValueKind != JsonValueKind.Number || item.GetRawText() != "1")
            throw new FormatException("DTR-DebtSchema: unsupported schema_version");
    }

    internal static string Hash(string value, int length)
    {
        if (value.Length != length || value.Any(c => c is not (>= '0' and <= '9' or >= 'a' and <= 'f')))
            throw new FormatException("DTR-DebtSchema: lowercase hash required");
        return value;
    }

    internal static string Sha256(ReadOnlySpan<byte> bytes) =>
        Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant();

    // The character ranges and escaping are the pinned Lean 4 Name.toString
    // contract (Init.Meta.Defs and Init.Data.ToString.Name), not .NET's broader
    // Unicode identifier classes. Quoted components retain embedded dots.
    internal static string Name(string value)
    {
        if (value.Length == 0 || Utf8.GetByteCount(value) > 1024)
            throw new FormatException("DTR-DebtSchema: noncanonical Name");
        var index = 0;
        while (index < value.Length)
        {
            if (value[index] == '«')
            {
                var end = value.IndexOf('»', index + 1);
                if (end < 0 || PlainIdentifier(value[(index + 1)..end]))
                    throw new FormatException("DTR-DebtSchema: noncanonical quoted Name");
                index = end + 1;
            }
            else
            {
                var end = value.IndexOf('.', index);
                if (end < 0) end = value.Length;
                var part = value[index..end];
                if (!PlainIdentifier(part) && !(part.Length > 0 && part.All(char.IsAsciiDigit)
                    && (part.Length == 1 || part[0] != '0')))
                    throw new FormatException("DTR-DebtSchema: noncanonical Name component");
                index = end;
            }

            if (index == value.Length) return value;
            if (value[index++] != '.' || index == value.Length)
                throw new FormatException("DTR-DebtSchema: noncanonical Name separator");
        }

        throw new FormatException("DTR-DebtSchema: empty Name");
    }

    private static bool PlainIdentifier(string value)
    {
        var runes = value.EnumerateRunes().ToArray();
        return runes.Length > 0 && IdFirst(runes[0].Value)
            && runes.Skip(1).All(r => IdFirst(r.Value) || r.Value is >= '0' and <= '9'
                or '\'' or '!' or '?' or >= 0x2080 and <= 0x2089 or >= 0x2090 and <= 0x209c
                or >= 0x1d62 and <= 0x1d6a or 0x2c7c);
    }

    private static bool IdFirst(int c) => c is >= 'a' and <= 'z' or >= 'A' and <= 'Z' or '_'
        || c is >= 0x3b1 and <= 0x3c9 && c != 0x3bb
        || c is >= 0x391 and <= 0x3a9 && c is not (0x3a0 or 0x3a3)
        || c is >= 0x3ca and <= 0x3fb or >= 0x1f00 and <= 0x1ffe
            or >= 0x2100 and <= 0x214f or >= 0x1d49c and <= 0x1d59f
        || c is >= 0xc0 and <= 0xff && c is not (0xd7 or 0xf7)
        || c is >= 0x100 and <= 0x17f;
}
