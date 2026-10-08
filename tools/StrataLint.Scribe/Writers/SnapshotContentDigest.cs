using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe;

/// Adapts an Engine <see cref="RepositorySnapshot"/> to the package-owned
/// <see cref="TruthGraphSnapshotIdentity"/> digest. Knowing which repository paths are generated
/// projections uses Engine's <see cref="GeneratedArtifactInventory"/> identity contract; the
/// digest bytes are produced by Trureturing.Truth so downstream consumers can verify them.
public static class SnapshotContentDigest
{
    public static string ComputeContentHashes(
        IReadOnlyDictionary<string, ReadOnlyMemory<byte>> contentHashes, IEnumerable<string> documentPaths)
    {
        ArgumentNullException.ThrowIfNull(contentHashes);
        ArgumentNullException.ThrowIfNull(documentPaths);
        var generatedPaths = GeneratedArtifactInventory.Create(documentPaths)
            .Select(static artifact => artifact.Path).ToHashSet(StringComparer.Ordinal);
        return TruthGraphSnapshotIdentity.ComputeContentHashes(contentHashes.Select(pair =>
            new SnapshotContentHashEntry(pair.Key, pair.Value, generatedPaths.Contains(pair.Key))));
    }

    public static string Compute(
        RepositorySnapshot snapshot,
        IEnumerable<string> documentPaths)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(documentPaths);
        var generatedPaths = GeneratedArtifactInventory.Create(documentPaths)
            .Select(static artifact => artifact.Path)
            .ToHashSet(StringComparer.Ordinal);
        if (snapshot.Files.Values.Any(file => !file.ContentWasRead && !generatedPaths.Contains(file.Path.Value)))
            throw new ArgumentException("A full snapshot content digest requires every original non-projection file body.", nameof(snapshot));
        return TruthGraphSnapshotIdentity.Compute(
            snapshot.Files.Values.Select(file => new SnapshotDigestEntry(
                file.Path.Value,
                file.RawBytes.AsMemory(),
                generatedPaths.Contains(file.Path.Value))));
    }
}
