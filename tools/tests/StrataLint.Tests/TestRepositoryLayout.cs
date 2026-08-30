namespace StrataLint.Tests;

internal readonly record struct RepositoryRelativePath
{
    private RepositoryRelativePath(string value) => Value = value;

    internal string Value { get; }

    internal static RepositoryRelativePath Create(string value)
    {
        if (string.IsNullOrWhiteSpace(value)
            || Path.IsPathRooted(value)
            || value.Split('/', '\\').Any(static segment => segment is "" or "." or ".."))
        {
            throw new ArgumentException(
                "repository path must be a normalized relative path",
                nameof(value));
        }

        return new RepositoryRelativePath(value.Replace('\\', '/'));
    }
}

internal static class TestRepositoryLayout
{
    internal static string ReadAllText(RepositoryRelativePath path) => File.ReadAllText(
        Path.Combine(FindRoot(), path.Value.Replace('/', Path.DirectorySeparatorChar)));

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

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
