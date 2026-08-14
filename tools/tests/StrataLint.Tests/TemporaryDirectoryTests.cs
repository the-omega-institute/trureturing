namespace StrataLint.Tests;

public sealed class TemporaryDirectoryTests
{
    [Fact]
    public void CleanupRetriesTransientDirectoryNotEmptyAndFailsClosedWhenItPersists()
    {
        var transientAttempts = 0;
        var transientDelays = 0;

        TestDirectoryCleanup.DeleteRecursively(
            "transient",
            (_, recursive) =>
            {
                Assert.True(recursive);
                transientAttempts++;
                if (transientAttempts < 3)
                {
                    throw new IOException("Directory not empty");
                }
            },
            _ => transientDelays++);

        Assert.Equal(3, transientAttempts);
        Assert.Equal(2, transientDelays);

        var persistentAttempts = 0;
        var exception = Assert.Throws<IOException>(() =>
            TestDirectoryCleanup.DeleteRecursively(
                "persistent",
                (_, _) =>
                {
                    persistentAttempts++;
                    throw new IOException("Directory not empty");
                },
                _ => { }));

        Assert.Equal(TestDirectoryCleanup.MaximumAttempts, persistentAttempts);
        Assert.Equal("Directory not empty", exception.Message);
    }

    [Fact]
    public void DiscoveryFrameworkDisposalDoesNotDeleteExecutionScratch()
    {
        using var framework = new TestScratchFramework(new Xunit.Sdk.NullMessageSink());
        using var directory = new TemporaryDirectory();

        framework.Dispose();

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
