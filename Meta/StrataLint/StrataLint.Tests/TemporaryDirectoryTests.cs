namespace StrataLint.Tests;

public sealed class TemporaryDirectoryTests
{
    [Fact]
    public async Task DiscoveryFrameworkDisposalDoesNotDeleteExecutionScratch()
    {
        using var framework = new TestScratchFramework(new Xunit.Sdk.NullMessageSink());
        using var directory = new TemporaryDirectory();

        framework.Dispose();
        await Task.Delay(100);

        Assert.True(Directory.Exists(directory.Path));
    }

    [Fact]
    public void RunRootDeletesUndisposedDirectoryAfterSetupAssertion()
    {
        string? rootPath = null;
        string? directoryPath = null;

        var exception = Record.Exception(() =>
        {
            using var root = new TestScratchRoot();
            rootPath = root.Path;
            directoryPath = root.CreateDirectory();
            File.WriteAllText(Path.Combine(directoryPath, "artifact.txt"), "fixture\n");

            Assert.Fail("synthetic fixture setup failure");
        });

        Assert.NotNull(exception);
        Assert.Equal("synthetic fixture setup failure", exception.Message);
        Assert.False(Directory.Exists(directoryPath));
        Assert.False(Directory.Exists(rootPath));
    }

    [Fact]
    public void DirectoriesBelongToOneRunScratchRoot()
    {
        using var first = new TemporaryDirectory();
        using var second = new TemporaryDirectory();

        var firstRoot = Directory.GetParent(first.Path)!.FullName;
        var secondRoot = Directory.GetParent(second.Path)!.FullName;

        Assert.Equal(firstRoot, secondRoot);
        Assert.StartsWith(
            "stratalint-tests-",
            Path.GetFileName(firstRoot),
            StringComparison.Ordinal);
    }
}
