namespace StrataLint.ArchitectureTests;

internal static class GitIndexRepositoryFiles
{
    internal static IReadOnlyList<(string RelativePath, string FullPath)> Enumerate(
        string repositoryRoot) => StrataLint.Engine.GitIndexRepositoryFiles.Enumerate(repositoryRoot);

    /// <summary>
    /// Returns tracked files under <paramref name="declaredPrefix"/>.
    /// </summary>
    internal static IReadOnlyList<(string RelativePath, string FullPath)> EnumerateDeclared(
        string repositoryRoot,
        string declaredPrefix) =>
        StrataLint.Engine.GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(file => file.RelativePath.StartsWith(declaredPrefix + "/", StringComparison.Ordinal))
            .ToArray();
}
