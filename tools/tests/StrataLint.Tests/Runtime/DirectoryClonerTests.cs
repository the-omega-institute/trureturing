using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class DirectoryClonerTests
{
    [Fact]
    public void CloneReproducesTheWholeTreeInOneCall()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var scratch = new TemporaryDirectory();
        var source = Path.Combine(scratch.Path, "donor");
        Directory.CreateDirectory(Path.Combine(source, "build", "lib"));
        File.WriteAllText(Path.Combine(source, "build", "lib", "Mathlib.olean"), "olean bytes\n");
        File.WriteAllText(Path.Combine(source, "build", "manifest"), "manifest\n");
        File.CreateSymbolicLink(Path.Combine(source, "current"), "build/lib");
        var target = Path.Combine(scratch.Path, "clone");

        var failure = new ApfsDirectoryCloner().Clone(source, target);

        Assert.Null(failure);
        Assert.Equal(
            "olean bytes\n",
            File.ReadAllText(Path.Combine(target, "build", "lib", "Mathlib.olean")));
        Assert.Equal("manifest\n", File.ReadAllText(Path.Combine(target, "build", "manifest")));
        Assert.Equal("build/lib", new FileInfo(Path.Combine(target, "current")).LinkTarget);
    }

    [Fact]
    public void CloneLeavesTheDonorUntouchedByLaterWrites()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var scratch = new TemporaryDirectory();
        var source = Path.Combine(scratch.Path, "donor");
        Directory.CreateDirectory(source);
        var donorFile = Path.Combine(source, "cache.bin");
        File.WriteAllText(donorFile, "warm cache\n");
        var target = Path.Combine(scratch.Path, "clone");

        Assert.Null(new ApfsDirectoryCloner().Clone(source, target));
        File.WriteAllText(donorFile, "donor changed\n");

        Assert.Equal("warm cache\n", File.ReadAllText(Path.Combine(target, "cache.bin")));
    }

    [Fact]
    public void CloneReportsTheSystemErrorTextWhenTheSourceIsMissing()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var scratch = new TemporaryDirectory();

        var failure = new ApfsDirectoryCloner().Clone(
            Path.Combine(scratch.Path, "absent"),
            Path.Combine(scratch.Path, "clone"));

        Assert.NotNull(failure);
        Assert.Contains("clonefile", failure, StringComparison.Ordinal);
        Assert.Contains("No such file", failure, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void CloneRefusesATargetThatAlreadyExists()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var scratch = new TemporaryDirectory();
        var source = Path.Combine(scratch.Path, "donor");
        Directory.CreateDirectory(source);
        File.WriteAllText(Path.Combine(source, "cache.bin"), "warm cache\n");
        var target = Path.Combine(scratch.Path, "clone");
        Directory.CreateDirectory(target);

        var failure = new ApfsDirectoryCloner().Clone(source, target);

        Assert.NotNull(failure);
        Assert.Contains("File exists", failure, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void CloneRefusesToRunOffMacOs()
    {
        if (OperatingSystem.IsMacOS()) return;
        using var scratch = new TemporaryDirectory();
        var source = Path.Combine(scratch.Path, "donor");
        Directory.CreateDirectory(source);

        var failure = new ApfsDirectoryCloner().Clone(source, Path.Combine(scratch.Path, "clone"));

        Assert.NotNull(failure);
        Assert.Contains("macOS", failure, StringComparison.Ordinal);
    }

    [Fact]
    public void CloneCarriesNonAsciiPathsThroughUnchanged()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var scratch = new TemporaryDirectory();
        var source = Path.Combine(scratch.Path, "供体-café");
        Directory.CreateDirectory(source);
        File.WriteAllText(Path.Combine(source, "缓存.bin"), "warm cache\n", new UTF8Encoding(false));
        var target = Path.Combine(scratch.Path, "克隆-café");

        Assert.Null(new ApfsDirectoryCloner().Clone(source, target));

        Assert.Equal("warm cache\n", File.ReadAllText(Path.Combine(target, "缓存.bin")));
    }
}
