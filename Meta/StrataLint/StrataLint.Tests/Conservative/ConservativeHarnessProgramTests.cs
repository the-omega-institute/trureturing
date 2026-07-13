using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ConservativeHarnessProgramTests
{
    [Fact]
    public void RuntimeDependencyBytesContributeToHarnessRoot()
    {
        using var temporary = new TemporaryDirectory();
        var source = Path.Combine(
            FindRepositoryRoot(),
            "Meta",
            "StrataLint",
            "StrataLint.Cli",
            "bin",
            "Release",
            "net10.0");
        var target = Path.Combine(
            temporary.Path,
            "Meta",
            "StrataLint",
            "StrataLint.Cli",
            "bin",
            "Release",
            "net10.0");
        Directory.CreateDirectory(target);
        foreach (var path in Directory.EnumerateFiles(source))
        {
            File.Copy(path, Path.Combine(target, Path.GetFileName(path)));
        }

        var environment = new ProductionConservativeExtensionEnvironment();
        var before = environment.LoadHarness(temporary.Path);
        using (var dependency = new FileStream(
            Path.Combine(target, "YamlDotNet.dll"),
            FileMode.Append,
            FileAccess.Write,
            FileShare.None))
        {
            dependency.WriteByte(0);
        }

        var after = environment.LoadHarness(temporary.Path);

        Assert.NotEqual(before.Root, after.Root);
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
