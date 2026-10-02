using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;

namespace StrataLint.Scribe;

public enum ScribeResourcePackErrorCode
{
    InvalidArchive, InvalidManifest, MissingManifest, SchemaMismatch, VersionMismatch,
    DuplicateGid, DuplicatePath, MissingEntry, UnexpectedEntry, EntryDigestMismatch,
    TotalDigestMismatch,
}

public sealed class ScribeResourcePackException : FormatException
{
    public ScribeResourcePackException(ScribeResourcePackErrorCode reasonCode, string message, Exception? inner = null)
        : base($"{reasonCode}: {message}", inner) => ReasonCode = reasonCode;

    public ScribeResourcePackErrorCode ReasonCode { get; }
}

public sealed record ScribeResourcePackEntry(string Path, string Gid, string Sha256, string InputKey);

public sealed record ScribeResourcePackManifest(
    string Schema, int Version, int EntryCount, ImmutableArray<ScribeResourcePackEntry> Entries, string TotalSha256)
{
    public long TotalUncompressedBytes { get; internal init; }
}

public sealed class ScribeResourcePack
{
    public const string SchemaName = "trureturing.scribe.resource-pack";
    public const int SemanticVersion = 2;
    private static readonly DateTimeOffset EntryTimestamp = new(1980, 1, 1, 0, 0, 0, TimeSpan.Zero);
    private readonly IReadOnlyDictionary<string, byte[]> resources;

    private ScribeResourcePack(ScribeResourcePackManifest manifest, IReadOnlyDictionary<string, byte[]> resources)
    {
        Manifest = manifest;
        this.resources = resources;
    }

    public ScribeResourcePackManifest Manifest { get; }
    public long TotalUncompressedBytes => Manifest.TotalUncompressedBytes;

    public static ScribeResourcePackManifest Write(string path,
        IEnumerable<(DocumentDefinition Definition, string InputKey)> definitions)
    {
        ArgumentNullException.ThrowIfNull(definitions);
        return WriteEncoded(path, definitions.Select(item =>
        {
            ArgumentNullException.ThrowIfNull(item.Definition);
            return (item.Definition.Document.Header.Gid.Value, item.InputKey, ScribeResourceCodec.Encode(item.Definition));
        }));
    }

    internal static ScribeResourcePackManifest WriteEncoded(string path,
        IEnumerable<(string Gid, string InputKey, byte[] Bytes)> resources)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(path);
        var ordered = resources.Select(item => (Path: ResourcePath(item.Gid), item.Gid, item.InputKey, item.Bytes))
            .OrderBy(item => item.Path, StringComparer.Ordinal).ToArray();
        RequireUnique(ordered.Select(item => item.Gid), ScribeResourcePackErrorCode.DuplicateGid);
        RequireUnique(ordered.Select(item => item.Path), ScribeResourcePackErrorCode.DuplicatePath);
        if (ordered.Any(item => !ScribeResourcePackManifestCodec.IsDigest(item.InputKey)))
            throw Error(ScribeResourcePackErrorCode.InvalidManifest, "Input keys require lowercase SHA-256 digests.");

        var entries = ImmutableArray.CreateBuilder<ScribeResourcePackEntry>(ordered.Length);
        var totalBytes = 0L;
        using var file = File.Create(path);
        using var zip = new ZipArchive(file, ZipArchiveMode.Create);
        foreach (var item in ordered)
        {
            var bytes = item.Bytes;
            totalBytes = checked(totalBytes + bytes.LongLength);
            entries.Add(new ScribeResourcePackEntry(item.Path, item.Gid, Digest(bytes), item.InputKey));
            WriteEntry(zip, item.Path, bytes);
        }
        var list = entries.ToImmutable();
        var manifest = new ScribeResourcePackManifest(SchemaName, SemanticVersion, list.Length, list,
            Digest(ScribeResourcePackManifestCodec.EncodeEntries(list))) { TotalUncompressedBytes = totalBytes };
        WriteEntry(zip, "manifest.json", ScribeResourcePackManifestCodec.Encode(manifest));
        return manifest;
    }

    public static ScribeResourcePack Open(string path)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(path);
        try
        {
            using var file = File.OpenRead(path);
            using var zip = new ZipArchive(file, ZipArchiveMode.Read);
            RequireUnique(zip.Entries.Select(item => item.FullName), ScribeResourcePackErrorCode.DuplicatePath);
            var manifestEntry = zip.GetEntry("manifest.json")
                ?? throw Error(ScribeResourcePackErrorCode.MissingManifest, "The archive has no manifest.json.");
            var manifest = ScribeResourcePackManifestCodec.Decode(ReadEntry(manifestEntry));
            var physical = zip.Entries.Where(item => item.FullName != "manifest.json")
                .ToDictionary(item => item.FullName, StringComparer.Ordinal);
            var expected = manifest.Entries.Select(item => item.Path).ToHashSet(StringComparer.Ordinal);
            var missing = expected.Except(physical.Keys, StringComparer.Ordinal).FirstOrDefault();
            if (missing is not null)
                throw Error(ScribeResourcePackErrorCode.MissingEntry, $"Missing resource: {missing}.");
            var extra = physical.Keys.Except(expected, StringComparer.Ordinal).FirstOrDefault();
            if (extra is not null)
                throw Error(ScribeResourcePackErrorCode.UnexpectedEntry, $"Unexpected resource: {extra}.");

            var resources = new Dictionary<string, byte[]>(StringComparer.Ordinal);
            var totalBytes = 0L;
            foreach (var entry in manifest.Entries)
            {
                var bytes = ReadEntry(physical[entry.Path]);
                if (!string.Equals(Digest(bytes), entry.Sha256, StringComparison.Ordinal))
                    throw Error(ScribeResourcePackErrorCode.EntryDigestMismatch, $"Resource digest differs: {entry.Path}.");
                totalBytes = checked(totalBytes + bytes.LongLength);
                resources.Add(entry.Gid, bytes);
            }
            return new ScribeResourcePack(manifest with { TotalUncompressedBytes = totalBytes }, resources);
        }
        catch (InvalidDataException exception)
        {
            throw new ScribeResourcePackException(ScribeResourcePackErrorCode.InvalidArchive,
                "The input is not a readable zip resource pack.", exception);
        }
    }

    public DocumentDefinition Read(string gid)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(gid);
        return ScribeResourceCodec.Decode(resources[gid], expectedGid: gid,
            expectedSourcePath: "Blueprint/" + gid + ".scribe.cs");
    }

    internal ReadOnlySpan<byte> EncodedBytes(string gid) => resources[gid];

    public IEnumerable<DocumentDefinition> ReadAll() => Manifest.Entries.Select(entry => Read(entry.Gid));

    internal static string ResourcePath(string gid)
    {
        if (!GidRef.Create(gid).IsFormalModule)
            throw Error(ScribeResourcePackErrorCode.InvalidManifest, "A resource GID must identify a formal module.");
        return gid + ".scribe.json";
    }

    internal static string Digest(byte[] bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));

    internal static void RequireUnique(IEnumerable<string> values, ScribeResourcePackErrorCode reason)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var value in values)
            if (!seen.Add(value)) throw Error(reason, $"Repeated identity: {value}.");
    }

    private static void WriteEntry(ZipArchive zip, string path, byte[] bytes)
    {
        var entry = zip.CreateEntry(path, CompressionLevel.Optimal);
        entry.LastWriteTime = EntryTimestamp;
        using var stream = entry.Open();
        stream.Write(bytes);
    }

    private static byte[] ReadEntry(ZipArchiveEntry entry)
    {
        using var stream = entry.Open();
        using var buffer = new MemoryStream();
        stream.CopyTo(buffer);
        return buffer.ToArray();
    }

    private static ScribeResourcePackException Error(ScribeResourcePackErrorCode reason, string message) => new(reason, message);
}
