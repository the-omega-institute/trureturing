namespace StrataLint.ArchitectureTests;

internal static class CSharpRepositorySources
{
    internal static IEnumerable<(string RelativePath, string FullPath)> Enumerate(
        string repositoryRoot) => GitIndexRepositoryFiles.Enumerate(repositoryRoot)
        .Where(static file => file.RelativePath.EndsWith(".cs", StringComparison.Ordinal));

    internal static HashSet<string> ExistingFiles(string repositoryRoot) =>
        GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Select(static file => file.RelativePath)
            .ToHashSet(StringComparer.Ordinal);
}
