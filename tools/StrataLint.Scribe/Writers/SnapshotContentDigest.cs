using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe;

/// Adapts an Engine <see cref="RepositorySnapshot"/> to the package-owned
/// <see cref="TruthGraphSnapshotIdentity"/> digest. Knowing which repository paths are generated
/// projections is Scribe's responsibility (it owns <see cref="GeneratedArtifactInventory"/>); the
/// digest bytes are produced by Trureturing.Truth so downstream consumers can verify them.
public static class SnapshotContentDigest
{
    public static string Compute(
        RepositorySnapshot snapshot,
        IEnumerable<string> documentPaths)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(documentPaths);
        var generatedPaths = GeneratedArtifactInventory.Create(documentPaths)
            .Select(static artifact => artifact.Path)
            .ToHashSet(StringComparer.Ordinal);
        return TruthGraphSnapshotIdentity.Compute(
            snapshot.Files.Values.Select(file => new SnapshotDigestEntry(
                file.Path.Value,
                file.RawBytes.AsMemory(),
                generatedPaths.Contains(file.Path.Value))));
    }
}
