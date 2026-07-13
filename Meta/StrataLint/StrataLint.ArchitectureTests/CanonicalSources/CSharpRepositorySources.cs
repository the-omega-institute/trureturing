namespace StrataLint.ArchitectureTests;

internal static class CSharpRepositorySources
{
    internal static IEnumerable<(string RelativePath, string FullPath)> Enumerate(string repositoryRoot)
    {
        foreach (var path in Directory.EnumerateFiles(repositoryRoot, "*.cs", SearchOption.AllDirectories))
        {
            var relativePath = Path.GetRelativePath(repositoryRoot, path).Replace('\\', '/');
            if (relativePath.Split('/').Any(static segment =>
                    segment is ".git" or ".lake" or "bin" or "obj"))
            {
                continue;
            }

            yield return (relativePath, path);
        }
    }

    internal static HashSet<string> ExistingFiles(string repositoryRoot) =>
        Directory.EnumerateFiles(repositoryRoot, "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(repositoryRoot, path).Replace('\\', '/'))
            .Where(static path => !path.Split('/').Any(static segment =>
                segment is ".git" or ".lake" or "bin" or "obj"))
            .ToHashSet(StringComparer.Ordinal);
}
