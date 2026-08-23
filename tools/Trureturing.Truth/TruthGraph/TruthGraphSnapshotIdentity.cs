using System.Buffers.Binary;
using System.Security.Cryptography;
using System.Text;

namespace Trureturing.Truth;

/// One repository file's contribution to the snapshot content digest. Generated projections are
/// folded in by a fixed marker rather than their bytes, so re-emitting them never changes identity.
public readonly record struct SnapshotDigestEntry(
    string Path,
    ReadOnlyMemory<byte> Content,
    bool IsGeneratedProjection);

/// Computes the truth-graph snapshot content digest recorded in
/// <see cref="TruthGraphProvenance.SnapshotContentDigest"/>. The algorithm is self-contained so a
/// downstream consumer can recompute and verify the digest from its own repository state; deciding
/// which paths are generated projections is a producer concern supplied through
/// <see cref="SnapshotDigestEntry.IsGeneratedProjection"/>.
public static class TruthGraphSnapshotIdentity
{
    private static readonly byte[] ProjectionMarker = Encoding.UTF8.GetBytes("scribe-generated-projection-v1");

    public static string Compute(IEnumerable<SnapshotDigestEntry> files)
    {
        ArgumentNullException.ThrowIfNull(files);
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        Append(hash, "repository-snapshot-v1");
        foreach (var file in files.OrderBy(static file => file.Path, StringComparer.Ordinal))
        {
            Append(hash, file.Path);
            var contentHash = file.IsGeneratedProjection
                ? SHA256.HashData(ProjectionMarker)
                : SHA256.HashData(file.Content.Span);
            Append(hash, contentHash);
        }

        return "sha256:" + Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    private static void Append(IncrementalHash hash, string value) => Append(hash, Encoding.UTF8.GetBytes(value));

    private static void Append(IncrementalHash hash, ReadOnlySpan<byte> value)
    {
        Span<byte> length = stackalloc byte[sizeof(int)];
        BinaryPrimitives.WriteInt32LittleEndian(length, value.Length);
        hash.AppendData(length);
        hash.AppendData(value);
    }
}
