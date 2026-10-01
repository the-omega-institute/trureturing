using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json.Nodes;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeResourcePackTests
{
    [Theory]
    [InlineData("MissingManifest")]
    [InlineData("UnexpectedEntry")]
    [InlineData("MissingEntry")]
    [InlineData("EntryDigestMismatch")]
    [InlineData("TotalDigestMismatch")]
    [InlineData("SchemaMismatch")]
    [InlineData("VersionMismatch")]
    [InlineData("DuplicateGid")]
    [InlineData("DuplicatePath")]
    [InlineData("InvalidManifest")]
    [InlineData("InvalidArchive")]
    public void ReaderRejectsEachMalformedPackWithNamedReason(string reason)
    {
        using var root = new TemporaryRoot();
        var path = root.Resolve("resources.zip");
        ScribeResourcePack.Write(path, [Definition("First"), Definition("Second")]);
        var entries = ReadZip(path);
        var manifest = JsonNode.Parse(entries.Single(item => item.Name == "manifest.json").Bytes)!.AsObject();
        switch (reason)
        {
            case "MissingManifest": entries.RemoveAll(item => item.Name == "manifest.json"); break;
            case "UnexpectedEntry": entries.Add(("extra.json", Encoding.UTF8.GetBytes("{}"))); break;
            case "MissingEntry": entries.RemoveAt(0); break;
            case "EntryDigestMismatch": entries[0].Bytes[0] ^= 1; break;
            case "TotalDigestMismatch": manifest["totalSha256"] = new string('0', 64); break;
            case "SchemaMismatch": manifest["schema"] = "unknown"; break;
            case "VersionMismatch": manifest["version"] = 2; break;
            case "DuplicateGid": manifest["entries"]![1]!["gid"] = manifest["entries"]![0]!["gid"]!.DeepClone(); break;
            case "DuplicatePath": manifest["entries"]![1]!["path"] = manifest["entries"]![0]!["path"]!.DeepClone(); break;
            case "InvalidManifest": manifest["entryCount"] = 9; break;
            case "InvalidArchive":
                TemporaryFileSystem.File.WriteAllBytes(path, [0xff]);
                AssertReason(path, reason);
                return;
        }
        if (entries.Any(item => item.Name == "manifest.json"))
        {
            entries[entries.FindIndex(item => item.Name == "manifest.json")] =
                ("manifest.json", Encoding.UTF8.GetBytes(manifest.ToJsonString()));
        }
        RewriteZip(path, entries);

        AssertReason(path, reason);
    }

    [Fact]
    public void ReaderRejectsEntryDigestMismatch()
    {
        using var root = new TemporaryRoot();
        var path = root.Resolve("resources.zip");
        ScribeResourcePack.Write(path, [Definition("First")]);
        var entries = ReadZip(path);
        entries[0].Bytes[^1] ^= 1;
        RewriteZip(path, entries);

        AssertReason(path, "EntryDigestMismatch");
    }

    [Fact]
    public void WriterRejectsDuplicateGidsAndPathsBeforeCreatingOutput()
    {
        using var root = new TemporaryRoot();
        var path = root.Resolve("duplicate.zip");
        var definition = Definition("First");

        var error = Assert.Throws<ScribeResourcePackException>(() =>
            ScribeResourcePack.Write(path, [definition, definition]));

        Assert.Equal(ScribeResourcePackErrorCode.DuplicateGid, error.ReasonCode);
        Assert.False(File.Exists(path));
    }

    [Fact]
    public void ReaderRejectsDuplicatePhysicalEntryPaths()
    {
        using var root = new TemporaryRoot();
        var path = root.Resolve("duplicate.zip");
        ScribeResourcePack.Write(path, [Definition("First")]);
        var entries = ReadZip(path);
        entries.Add(entries[0]);
        RewriteZip(path, entries);

        AssertReason(path, "DuplicatePath");
    }

    [Fact]
    public void PackRoundTripsCanonicalBytesAndEnumeratesItsManifest()
    {
        using var root = new TemporaryRoot();
        var path = root.Resolve("resources.zip");
        var definitions = new[] { Definition("Second"), Definition("First") };
        var written = ScribeResourcePack.Write(path, definitions);
        var pack = ScribeResourcePack.Open(path);

        Assert.Equal(2, pack.Manifest.EntryCount);
        Assert.Equal(ScribeResourcePack.SchemaName, pack.Manifest.Schema);
        Assert.Equal(1, pack.Manifest.Version);
        Assert.Equal(written.TotalSha256, pack.Manifest.TotalSha256);
        Assert.Equal(definitions.Sum(item => (long)ScribeResourceCodec.Encode(item).Length), pack.TotalUncompressedBytes);
        Assert.Equal(["D5/S0/Synthetic/First.scribe.json", "D5/S0/Synthetic/Second.scribe.json"],
            pack.Manifest.Entries.Select(item => item.Path));
        Assert.Equal(2, pack.ReadAll().Count());
        foreach (var definition in definitions)
        {
            var bytes = ScribeResourceCodec.Encode(definition);
            Assert.Equal(bytes, ScribeResourceCodec.Encode(pack.Read(definition.Document.Header.Gid.Value)));
            var entry = pack.Manifest.Entries.Single(item => item.Gid == definition.Document.Header.Gid.Value);
            Assert.Equal(Convert.ToHexStringLower(SHA256.HashData(bytes)), entry.Sha256);
        }
        var list = "[" + string.Join(",", pack.Manifest.Entries.Select(item =>
            $"{{\"path\":\"{item.Path}\",\"gid\":\"{item.Gid}\",\"sha256\":\"{item.Sha256}\"}}")) + "]";
        Assert.Equal(Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(list))), pack.Manifest.TotalSha256);
        Assert.Throws<KeyNotFoundException>(() => pack.Read("D5/S0/Synthetic/Missing"));
        using var zip = new ZipArchive(new MemoryStream(File.ReadAllBytes(path)), ZipArchiveMode.Read);
        Assert.All(zip.Entries, item => Assert.Equal(new DateTime(1980, 1, 1, 0, 0, 0), item.LastWriteTime.DateTime));
    }

    [Fact]
    public void IdentityIgnoresPhysicalOrderCompressionAndTimestamps()
    {
        using var root = new TemporaryRoot();
        var path = root.Resolve("resources.zip");
        ScribeResourcePack.Write(path, [Definition("Second"), Definition("First")]);
        var original = ScribeResourcePack.Open(path).Manifest;
        var originalBytes = File.ReadAllBytes(path);
        var entries = ReadZip(path);
        entries.Reverse();
        RewriteZip(path, entries, new DateTimeOffset(2001, 2, 3, 4, 5, 6, TimeSpan.Zero));

        var rewritten = ScribeResourcePack.Open(path);
        Assert.Equal(original.TotalSha256, rewritten.Manifest.TotalSha256);
        Assert.Equal(original.Entries.ToArray(), rewritten.Manifest.Entries.ToArray());
        Assert.False(originalBytes.SequenceEqual(File.ReadAllBytes(path)));
        Assert.Equal(2, rewritten.ReadAll().Count());
    }

    internal static DocumentDefinition Definition(string name) => DocumentDefinition.Create(
        ScribeDocument.Create(DefinitionDsl.Header("D5/S0/Synthetic/" + name, "Resource fixture"),
            DefinitionDsl.H(name), DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("body")))),
        "Blueprint/D5/S0/Synthetic/" + name + ".scribe.cs");

    internal static List<(string Name, byte[] Bytes)> ReadZip(string path)
    {
        using var zip = new ZipArchive(new MemoryStream(File.ReadAllBytes(path)), ZipArchiveMode.Read);
        return zip.Entries.Select(item =>
        {
            using var stream = item.Open();
            using var buffer = new MemoryStream();
            stream.CopyTo(buffer);
            return (item.FullName, buffer.ToArray());
        }).ToList();
    }

    internal static void RewriteZip(string path, IEnumerable<(string Name, byte[] Bytes)> entries,
        DateTimeOffset? timestamp = null)
    {
        using var buffer = new MemoryStream();
        using (var zip = new ZipArchive(buffer, ZipArchiveMode.Create, leaveOpen: true))
        {
            foreach (var item in entries)
            {
                var entry = zip.CreateEntry(item.Name, CompressionLevel.NoCompression);
                entry.LastWriteTime = timestamp ?? new DateTimeOffset(1980, 1, 1, 0, 0, 0, TimeSpan.Zero);
                using var stream = entry.Open();
                stream.Write(item.Bytes);
            }
        }
        TemporaryFileSystem.File.WriteAllBytes(path, buffer.ToArray());
    }

    private static void AssertReason(string path, string reason)
    {
        var error = Assert.Throws<ScribeResourcePackException>(() => ScribeResourcePack.Open(path));
        Assert.Equal(reason, error.ReasonCode.ToString());
        Assert.Contains(reason + ":", error.Message, StringComparison.Ordinal);
    }
}
