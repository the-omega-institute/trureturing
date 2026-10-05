namespace StrataLint.TestSupport;

/// <summary>Candidate SDK configuration copied into synthetic Scribe repositories.</summary>
public static class ScribeSdkFixtureInputs
{
    public static IReadOnlyDictionary<string, string> Read() => new[]
    {
        "global.json", ".editorconfig", "Directory.Build.props", "Directory.Packages.props",
        "tools/Architecture/BannedSymbols.txt", "tools/Architecture/BannedSymbols.Determinism.txt",
        "tools/Architecture/BannedSymbols.Guid.txt",
    }.ToDictionary(path => path, path => TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(path)), StringComparer.Ordinal);

    public static void Write(string root)
    {
        foreach (var (path, text) in Read())
        {
            var destination = Path.Combine(root, path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            TemporaryFileSystem.File.WriteAllText(destination, text);
        }
        TemporaryFileSystem.File.WriteAllText(Path.Combine(root, "NuGet.Config"),
            "<configuration><packageSources><clear /></packageSources></configuration>");
    }
}
