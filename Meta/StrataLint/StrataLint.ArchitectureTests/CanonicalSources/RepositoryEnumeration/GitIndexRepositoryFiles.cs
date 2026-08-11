namespace StrataLint.ArchitectureTests;

internal static class GitIndexRepositoryFiles
{
    internal static IReadOnlyList<(string RelativePath, string FullPath)> Enumerate(
        string repositoryRoot) => StrataLint.Engine.GitIndexRepositoryFiles.Enumerate(repositoryRoot);
}
