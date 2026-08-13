namespace StrataLint.ArchitectureTests;

internal static class RepositoryLayout
{
    internal static string FindRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
            current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "global.json"))
                && Directory.Exists(Path.Combine(current.FullName, "tools")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate the repository root.");
    }
}
