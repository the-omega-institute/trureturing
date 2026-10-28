namespace StrataLint.ArchitectureTests;

internal static class GitIndexRepositoryFiles
{
    internal static IReadOnlyList<(string RelativePath, string FullPath)> Enumerate(
        string repositoryRoot) => StrataLint.Engine.GitRepositorySnapshotReader
        .ReadCurrentProjection(repositoryRoot, static _ => false).PathInventory
        .Where(static entry => entry.EffectiveMode is not null)
        .Select(entry => (RelativePath: entry.Path,
            FullPath: Path.Combine(repositoryRoot, entry.Path.Replace('/', Path.DirectorySeparatorChar))))
        .Where(static file => File.Exists(file.FullPath))
        .ToArray();

    /// <summary>
    /// Returns candidate files under <paramref name="declaredPrefix"/>.
    /// </summary>
    internal static IReadOnlyList<(string RelativePath, string FullPath)> EnumerateDeclared(
        string repositoryRoot,
        string declaredPrefix) =>
        Enumerate(repositoryRoot)
            .Where(file => file.RelativePath.StartsWith(declaredPrefix + "/", StringComparison.Ordinal))
            .ToArray();
}
