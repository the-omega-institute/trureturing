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
            if (!Canonical(document.RootElement).AsSpan().SequenceEqual(bytes))
            {
                document.Dispose();
                throw new FormatException("DTR-DebtSchema: noncanonical JSON bytes");
            }

            return document;
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

    internal static string Name(string value)
    {
        // Name v1: canonical unquoted identifier/numeric components. Reject ambiguous
        // spellings instead of silently coalescing escaped identifiers or empty parts.
        if (Utf8.GetByteCount(value) > 1024 || value.Split('.').Any(part =>
            part.Length == 0 || !(char.IsLetter(part[0]) || part[0] == '_'
                ? part.All(c => char.IsLetterOrDigit(c) || c is '_' or '\'')
                : part.All(char.IsAsciiDigit) && (part.Length == 1 || part[0] != '0'))))
            throw new FormatException("DTR-DebtSchema: noncanonical Name");
        return value;
    }
}
