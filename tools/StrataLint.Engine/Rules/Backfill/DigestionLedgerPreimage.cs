using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal static class DigestionLedgerPreimage
{
    private static readonly byte[] Header =
        Encoding.ASCII.GetBytes("stratalint-digestion-directory-ledger-v1\0");
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static string ComputeSha256(BackfillInventoryDocument document)
    {
        ArgumentNullException.ThrowIfNull(document);
        var files = document.RequireDigestionSources()
            .SelectMany(SourceFiles)
            .OrderBy(static file => file.Path, StringComparer.Ordinal)
            .ToArray();
        using var stream = new MemoryStream();
        stream.Write(Header);
        Span<byte> length = stackalloc byte[8];
        foreach (var file in files)
        {
            var path = StrictUtf8.GetBytes(file.Path);
            BinaryPrimitives.WriteInt32BigEndian(length[..4], path.Length);
            stream.Write(length[..4]);
            stream.Write(path);
            BinaryPrimitives.WriteInt64BigEndian(length, file.Bytes.Length);
            stream.Write(length);
            stream.Write(file.Bytes.AsSpan());
        }

        return DigestionFingerprint.ComputeOpaque(stream.ToArray()).RawSha256;
    }

    private static IEnumerable<LedgerFile> SourceFiles(DigestionLedgerSource source)
    {
        yield return new LedgerFile(
            $"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml",
            BackfillInventoryWriter.WriteSourceMetadata(source));
        foreach (var entry in source.Entries)
        {
            var state = DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)
                + "-"
                + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);
            yield return new LedgerFile(
                $"{BackfillInventoryLoader.RootPath}{source.SourceId}/{state}/{entry.AtomId}.yaml",
                BackfillInventoryWriter.WriteAtom(entry));
        }
    }

    private sealed record LedgerFile(string Path, ImmutableArray<byte> Bytes);
}
