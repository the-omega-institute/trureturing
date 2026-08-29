namespace StrataLint.ArchitectureTests;

public sealed class PortableShellLocaleTests
{
    [Fact]
    public void EveryPerlBackedShellScriptPinsThePortableLocale()
    {
        var unpinned = PerlBackedShellScriptInventory.PathsWithoutPortableLocale;

        Assert.True(
            unpinned.Length == 0,
            $"Perl-backed scripts without `export LC_ALL=C`: {string.Join(", ", unpinned)}");
    }
}

internal static class PerlBackedShellScriptInventory
{
    internal static string[] PathsWithoutPortableLocale
    {
        get
        {
            var root = RepositoryLayout.FindRoot();
            var scripts = Path.Combine(root, "tools", "scripts");
            return Directory.EnumerateFiles(scripts, "*.sh", SearchOption.AllDirectories)
                .Where(InvokesPerlBackedToolWithoutPortableLocale)
                .Select(path => Path.GetRelativePath(root, path))
                .Order(StringComparer.Ordinal)
                .ToArray();
        }
    }

    private static bool InvokesPerlBackedToolWithoutPortableLocale(string path)
    {
        var source = File.ReadAllText(path);
        var invokesPerlBackedTool = source
            .Split('\n')
            .Where(static line => !line.TrimStart().StartsWith('#'))
            .Any(static line => line.Contains("shasum", StringComparison.Ordinal)
                || line.Contains("perl", StringComparison.Ordinal));
        return invokesPerlBackedTool
            && !source.Split('\n').Contains("export LC_ALL=C", StringComparer.Ordinal);
    }
}
