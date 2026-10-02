using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;

namespace StrataLint.Scribe;

internal static class ScribeResourcePackManifestCodec
{
    internal static byte[] Encode(ScribeResourcePackManifest manifest) => JsonSerializer.SerializeToUtf8Bytes(
        new JsonObject
        {
            ["schema"] = manifest.Schema,
            ["version"] = manifest.Version,
            ["entryCount"] = manifest.EntryCount,
            ["entries"] = EntriesNode(manifest.Entries),
            ["totalSha256"] = manifest.TotalSha256,
        });

    /// <summary>The identity preimage is compact UTF-8 JSON of the path-sorted entry array.</summary>
    internal static byte[] EncodeEntries(ImmutableArray<ScribeResourcePackEntry> entries) =>
        JsonSerializer.SerializeToUtf8Bytes(EntriesNode(entries));

    private static JsonArray EntriesNode(ImmutableArray<ScribeResourcePackEntry> entries) => new(
        entries.Select(entry => (JsonNode)new JsonObject
        {
            ["path"] = entry.Path,
            ["gid"] = entry.Gid,
            ["sha256"] = entry.Sha256,
        }).ToArray());

    internal static ScribeResourcePackManifest Decode(byte[] bytes)
    {
        try
        {
            using var json = JsonDocument.Parse(bytes);
            var root = json.RootElement;
            RequireFields(root, "schema", "version", "entryCount", "entries", "totalSha256");
            var schema = String(root, "schema");
            if (schema != ScribeResourcePack.SchemaName)
                throw Error(ScribeResourcePackErrorCode.SchemaMismatch, "Unsupported resource pack schema.");
            var version = root.GetProperty("version").GetInt32();
            if (version != ScribeResourcePack.SemanticVersion)
                throw Error(ScribeResourcePackErrorCode.VersionMismatch, "Unsupported resource pack semantic version.");
            var entries = root.GetProperty("entries").EnumerateArray().Select(item =>
            {
                RequireFields(item, "path", "gid", "sha256");
                return new ScribeResourcePackEntry(String(item, "path"), String(item, "gid"), String(item, "sha256"));
            }).ToImmutableArray();
            var count = root.GetProperty("entryCount").GetInt32();
            if (count != entries.Length)
                throw Error(ScribeResourcePackErrorCode.InvalidManifest, "Entry count does not match the entry list.");
            ScribeResourcePack.RequireUnique(entries.Select(item => item.Gid), ScribeResourcePackErrorCode.DuplicateGid);
            ScribeResourcePack.RequireUnique(entries.Select(item => item.Path), ScribeResourcePackErrorCode.DuplicatePath);
            string? previous = null;
            foreach (var entry in entries)
            {
                if (entry.Path != ScribeResourcePack.ResourcePath(entry.Gid)
                    || previous is not null && StringComparer.Ordinal.Compare(previous, entry.Path) >= 0
                    || !IsDigest(entry.Sha256))
                    throw Error(ScribeResourcePackErrorCode.InvalidManifest, "Entries require canonical paths, ascending path order and lowercase SHA-256 digests.");
                previous = entry.Path;
            }
            var total = String(root, "totalSha256");
            if (!IsDigest(total) || total != ScribeResourcePack.Digest(EncodeEntries(entries)))
                throw Error(ScribeResourcePackErrorCode.TotalDigestMismatch, "Ordered entry list digest differs.");
            return new ScribeResourcePackManifest(schema, version, count, entries, total);
        }
        catch (ScribeResourcePackException) { throw; }
        catch (Exception exception) when (exception is JsonException or InvalidOperationException or FormatException or ArgumentException)
        {
            throw new ScribeResourcePackException(ScribeResourcePackErrorCode.InvalidManifest,
                "The manifest is not a valid resource pack manifest.", exception);
        }
    }

    private static void RequireFields(JsonElement value, params string[] fields)
    {
        if (value.ValueKind != JsonValueKind.Object)
            throw Error(ScribeResourcePackErrorCode.InvalidManifest, "Manifest objects must be JSON objects.");
        var names = value.EnumerateObject().Select(item => item.Name).ToArray();
        if (names.Length != fields.Length
            || names.Distinct(StringComparer.Ordinal).Count() != names.Length
            || fields.Except(names, StringComparer.Ordinal).Any())
            throw Error(ScribeResourcePackErrorCode.InvalidManifest, "Manifest fields must match the schema exactly.");
    }

    private static string String(JsonElement value, string name) => value.GetProperty(name).GetString()
        ?? throw Error(ScribeResourcePackErrorCode.InvalidManifest, $"Manifest field {name} cannot be null.");

    private static bool IsDigest(string value) => value.Length == 64
        && value.All(character => character is >= '0' and <= '9' or >= 'a' and <= 'f');

    private static ScribeResourcePackException Error(ScribeResourcePackErrorCode reason, string message) => new(reason, message);
}
