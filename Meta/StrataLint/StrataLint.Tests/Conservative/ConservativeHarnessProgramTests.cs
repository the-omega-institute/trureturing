using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ConservativeHarnessProgramTests
{
    [Fact]
    public void RuntimeDependencyBytesContributeToHarnessRoot()
    {
        using var temporary = new TemporaryDirectory();
        var source = AppContext.BaseDirectory;
        var target = Path.Combine(temporary.Path, "harness");
        Directory.CreateDirectory(target);
        foreach (var path in Directory.EnumerateFiles(source))
        {
            File.Copy(path, Path.Combine(target, Path.GetFileName(path)));
        }

        var targetDll = Path.Combine(target, "StrataLint.dll");
        var before = ProductionConservativeExtensionEnvironment.LoadHarnessAssembly(targetDll);
        using (var dependency = new FileStream(
            Path.Combine(target, "YamlDotNet.dll"),
            FileMode.Append,
            FileAccess.Write,
            FileShare.None))
        {
            dependency.WriteByte(0);
        }

        var after = ProductionConservativeExtensionEnvironment.LoadHarnessAssembly(targetDll);

        Assert.NotEqual(before.Root, after.Root);
    }
}
