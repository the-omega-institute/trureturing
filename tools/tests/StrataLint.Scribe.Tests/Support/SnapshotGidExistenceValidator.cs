using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class SnapshotGidExistenceValidator : IGidExistenceValidator
{
    private readonly RepositorySnapshot snapshot;

    public SnapshotGidExistenceValidator(RepositorySnapshot snapshot) =>
        this.snapshot = snapshot ?? throw new ArgumentNullException(nameof(snapshot));

    public bool Exists(GidRef reference)
    {
        ArgumentNullException.ThrowIfNull(reference);
        return snapshot.TryGetFile(reference.Path.Value, out _);
    }
}
