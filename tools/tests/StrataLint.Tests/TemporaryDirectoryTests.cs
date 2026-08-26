using System.Text.Json;

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
            () => transientDelays++);

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
                () => { }));

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

    [Fact]
    public void StartupSweepDeletesOnlyStaleUnlockedMatchingTopLevelRoots()
    {
        using var scanRoot = new TemporaryDirectory();
        var now = new DateTime(2030, 1, 2, 0, 0, 0, DateTimeKind.Utc);
        var stale = CreateSweepDirectory(scanRoot.Path, "stratalint-tests-stale", now.AddDays(-2));
        var recent = CreateSweepDirectory(scanRoot.Path, "stratalint-tests-recent", now.AddHours(-1));
        var other = CreateSweepDirectory(scanRoot.Path, "other-tests-stale", now.AddDays(-2));
        var nestedParent = CreateSweepDirectory(scanRoot.Path, "nested", now.AddDays(-2));
        var nested = CreateSweepDirectory(
            nestedParent,
            "stratalint-tests-nested",
            now.AddDays(-2));
        using var diagnostics = new StringWriter();

        TestScratchRootSweeper.Sweep(scanRoot.Path, now, diagnostics);

        Assert.False(Directory.Exists(stale));
        Assert.True(Directory.Exists(recent));
        Assert.True(Directory.Exists(other));
        Assert.True(Directory.Exists(nested));
    }

    [Fact]
    public void StartupSweepKeepsStaleRootWhileAnotherOwnerHoldsLease()
    {
        using var scanRoot = new TemporaryDirectory();
        var now = new DateTime(2030, 1, 2, 0, 0, 0, DateTimeKind.Utc);
        var active = CreateSweepDirectory(
            scanRoot.Path,
            "stratalint-tests-active",
            now.AddDays(-2));
        using var lease = new FileStream(
            Path.Combine(active, TestScratchRootSweeper.LeaseFileName),
            FileMode.CreateNew,
            FileAccess.ReadWrite,
            FileShare.None);
        Directory.SetLastWriteTimeUtc(active, now.AddDays(-2));
        using var diagnostics = new StringWriter();

        TestScratchRootSweeper.Sweep(scanRoot.Path, now, diagnostics);

        Assert.True(Directory.Exists(active));
    }

    [Fact]
    public void RunRootHoldsLeaseForItsLifetime()
    {
        using var root = new TestScratchRoot();
        var leasePath = Path.Combine(root.Path, TestScratchRootSweeper.LeaseFileName);

        Assert.Throws<IOException>(() =>
        {
            using var competingLease = new FileStream(
                leasePath,
                FileMode.Open,
                FileAccess.ReadWrite,
                FileShare.None);
        });
    }

    [Fact]
    public void StartupSweepRecordsDeleteFailureWithoutThrowing()
    {
        using var scanRoot = new TemporaryDirectory();
        var now = new DateTime(2030, 1, 2, 0, 0, 0, DateTimeKind.Utc);
        var stale = CreateSweepDirectory(scanRoot.Path, "stratalint-tests-stale", now.AddDays(-2));
        using var diagnostics = new StringWriter();

        var exception = Record.Exception(() =>
            TestScratchRootSweeper.Sweep(
                scanRoot.Path,
                now,
                diagnostics,
                _ => throw new IOException("injected cleanup failure")));

        Assert.Null(exception);
        Assert.True(Directory.Exists(stale));
        const string prefix = "TEST_SCRATCH_SWEEP ";
        var record = Assert.Single(
            diagnostics.ToString().Split('\n', StringSplitOptions.RemoveEmptyEntries));
        Assert.StartsWith(prefix, record, StringComparison.Ordinal);
        using var document = JsonDocument.Parse(record[prefix.Length..]);
        var root = document.RootElement;
        Assert.Equal("test-scratch-sweep-v1", root.GetProperty("schema").GetString());
        Assert.Equal("delete", root.GetProperty("operation").GetString());
        Assert.Equal("failed", root.GetProperty("status").GetString());
        Assert.Equal(stale, root.GetProperty("path").GetString());
        Assert.Equal(typeof(IOException).FullName, root.GetProperty("exception_type").GetString());
    }

    private static string CreateSweepDirectory(
        string parent,
        string name,
        DateTime lastWriteTimeUtc)
    {
        var path = Path.Combine(parent, name);
        Directory.CreateDirectory(path);
        File.WriteAllText(Path.Combine(path, "artifact.txt"), "fixture\n");
        Directory.SetLastWriteTimeUtc(path, lastWriteTimeUtc);
        return path;
    }
}
