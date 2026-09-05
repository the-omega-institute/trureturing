namespace StrataLint.Engine;

internal enum DerivationInputProjectionMode
{
    Sparse,
    Full,
}

internal sealed record EffectiveDerivationInputProjection
{
    private EffectiveDerivationInputProjection(
        RepositorySnapshot snapshot,
        DerivationInputProjectionMode mode,
        IReadOnlyList<RepositoryFile> files)
    {
        Snapshot = snapshot;
        Mode = mode;
        Files = files;
    }

    internal RepositorySnapshot Snapshot { get; }

    internal DerivationInputProjectionMode Mode { get; }

    internal IReadOnlyList<RepositoryFile> Files { get; }

    internal bool RequiresFullSnapshot => Mode == DerivationInputProjectionMode.Full;

    internal bool Contains(string path) =>
        RequiresFullSnapshot && Snapshot.TryGetFile(path, out _)
        || Files.Any(file => file.Path.Value == path);

    internal static EffectiveDerivationInputProjection Sparse(
        RepositorySnapshot snapshot,
        IEnumerable<RepositoryFile> files) =>
        new(
            snapshot,
            DerivationInputProjectionMode.Sparse,
            files.OrderBy(static file => file.Path.Value, StringComparer.Ordinal).ToArray());

    internal static EffectiveDerivationInputProjection Full(RepositorySnapshot snapshot) =>
        new(
            snapshot,
            DerivationInputProjectionMode.Full,
            snapshot.Files.Values.OrderBy(
                static file => file.Path.Value,
                StringComparer.Ordinal).ToArray());
}
