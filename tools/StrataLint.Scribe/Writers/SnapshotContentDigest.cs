using System.Collections.Immutable;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe;

/// Adapts an Engine <see cref="RepositorySnapshot"/> to the package-owned
/// <see cref="TruthGraphSnapshotIdentity"/> digest. Knowing which repository paths are generated
/// projections is Scribe's responsibility (it owns <see cref="GeneratedArtifactInventory"/>); the
/// digest bytes are produced by Trureturing.Truth so downstream consumers can verify them.
public static class SnapshotContentDigest
{
    private static readonly ImmutableHashSet<string> GeneratedPaths = GeneratedArtifactInventory.All
        .Select(static artifact => artifact.Path)
        .ToImmutableHashSet(StringComparer.Ordinal);

    public static string Compute(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        return TruthGraphSnapshotIdentity.Compute(
            snapshot.Files.Values.Select(static file => new SnapshotDigestEntry(
                file.Path.Value,
                file.RawBytes.AsMemory(),
                GeneratedPaths.Contains(file.Path.Value))));
    }
}
