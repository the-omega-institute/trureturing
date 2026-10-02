using System.Text.Json;

namespace StrataLint.Scribe;

public sealed record ScribeReleaseIdentity(
    string Schema, string SourceCommit, int PackFormatVersion, int EntryCount, string TotalSha256);

public enum ScribeReleaseIdentityErrorCode
{
    InvalidJson, MissingField, ExtraField, DuplicateField, InvalidType, SchemaMismatch,
    InvalidSourceCommit, InvalidPackFormatVersion, InvalidEntryCount, InvalidTotalSha256,
}

public sealed class ScribeReleaseIdentityException : FormatException
{
    public ScribeReleaseIdentityException(ScribeReleaseIdentityErrorCode reasonCode, string message, Exception? inner = null)
        : base($"{reasonCode}: {message}", inner) => ReasonCode = reasonCode;

    public ScribeReleaseIdentityErrorCode ReasonCode { get; }
}

/// <summary>Strict release identity JSON with fixed field order and compact UTF-8 encoding.</summary>
public static class ScribeReleaseIdentityCodec
{
    public const string SchemaName = "trureturing.scribe.release-identity";
    private static readonly string[] Fields = ["schema", "sourceCommit", "packFormatVersion", "entryCount", "totalSha256"];

    public static byte[] Encode(ScribeReleaseIdentity identity)
    {
        ArgumentNullException.ThrowIfNull(identity);
        Validate(identity);
        using var stream = new MemoryStream();
        using (var writer = new Utf8JsonWriter(stream))
        {
            writer.WriteStartObject();
            writer.WriteString("schema", identity.Schema);
            writer.WriteString("sourceCommit", identity.SourceCommit);
            writer.WriteNumber("packFormatVersion", identity.PackFormatVersion);
            writer.WriteNumber("entryCount", identity.EntryCount);
            writer.WriteString("totalSha256", identity.TotalSha256);
            writer.WriteEndObject();
        }
        return stream.ToArray();
    }

    public static ScribeReleaseIdentity Decode(byte[] bytes)
    {
        ArgumentNullException.ThrowIfNull(bytes);
        try
        {
            using var document = JsonDocument.Parse(bytes);
            var root = document.RootElement;
            if (root.ValueKind != JsonValueKind.Object)
                throw Error(ScribeReleaseIdentityErrorCode.InvalidJson, "Release identity must be a JSON object.");
            var names = root.EnumerateObject().Select(item => item.Name).ToArray();
            if (names.Distinct(StringComparer.Ordinal).Count() != names.Length)
                throw Error(ScribeReleaseIdentityErrorCode.DuplicateField, "Release identity fields must be unique.");
            var extra = names.Except(Fields, StringComparer.Ordinal).FirstOrDefault();
            if (extra is not null)
                throw Error(ScribeReleaseIdentityErrorCode.ExtraField, $"Unexpected release identity field: {extra}.");
            var missing = Fields.Except(names, StringComparer.Ordinal).FirstOrDefault();
            if (missing is not null)
                throw Error(ScribeReleaseIdentityErrorCode.MissingField, $"Missing release identity field: {missing}.");
            var identity = new ScribeReleaseIdentity(String(root, "schema"), String(root, "sourceCommit"),
                Integer(root, "packFormatVersion"), Integer(root, "entryCount"), String(root, "totalSha256"));
            Validate(identity);
            return identity;
        }
        catch (JsonException exception)
        {
            throw new ScribeReleaseIdentityException(ScribeReleaseIdentityErrorCode.InvalidJson,
                "Release identity is not valid JSON.", exception);
        }
    }

    internal static bool IsHex(string? value, int length) => value is not null && value.Length == length
        && value.All(character => character is >= '0' and <= '9' or >= 'a' and <= 'f');

    private static string String(JsonElement root, string field)
    {
        var value = root.GetProperty(field);
        if (value.ValueKind != JsonValueKind.String)
            throw Error(ScribeReleaseIdentityErrorCode.InvalidType, $"Release identity field {field} must be a string.");
        return value.GetString()!;
    }

    private static int Integer(JsonElement root, string field)
    {
        var value = root.GetProperty(field);
        if (value.ValueKind != JsonValueKind.Number || !value.TryGetInt32(out var result))
            throw Error(ScribeReleaseIdentityErrorCode.InvalidType, $"Release identity field {field} must be a 32-bit integer.");
        return result;
    }

    private static void Validate(ScribeReleaseIdentity identity)
    {
        if (identity.Schema != SchemaName)
            throw Error(ScribeReleaseIdentityErrorCode.SchemaMismatch, "Unsupported release identity schema.");
        if (!IsHex(identity.SourceCommit, 40))
            throw Error(ScribeReleaseIdentityErrorCode.InvalidSourceCommit, "sourceCommit requires 40 lowercase hexadecimal characters.");
        if (identity.PackFormatVersion <= 0)
            throw Error(ScribeReleaseIdentityErrorCode.InvalidPackFormatVersion, "packFormatVersion must be positive.");
        if (identity.EntryCount < 0)
            throw Error(ScribeReleaseIdentityErrorCode.InvalidEntryCount, "entryCount must be nonnegative.");
        if (!IsHex(identity.TotalSha256, 64))
            throw Error(ScribeReleaseIdentityErrorCode.InvalidTotalSha256, "totalSha256 requires 64 lowercase hexadecimal characters.");
    }

    private static ScribeReleaseIdentityException Error(ScribeReleaseIdentityErrorCode reason, string message) => new(reason, message);
}
