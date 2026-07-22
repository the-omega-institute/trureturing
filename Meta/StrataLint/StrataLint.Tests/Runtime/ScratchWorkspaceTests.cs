using System.Globalization;
using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ScratchWorkspaceTests
{
    [Fact]
    public void NoindexRootIsUnderTempAndSpotlightExcluded()
    {
        var root = ScratchWorkspace.NoindexRoot;

        Assert.StartsWith(
            Path.GetFullPath(Path.GetTempPath()),
            Path.GetFullPath(root),
            StringComparison.Ordinal);
        Assert.EndsWith(".noindex", root, StringComparison.Ordinal);
    }

    [Fact]
    public void DeadOwnerScratchIsStaleEvenWhenYoung()
    {
        using var temp = new TempDir();
        var directory = CreateScratch(temp, "stratalint-c0-renew-alpha", ownerPid: 4242);
        TouchNow(directory);

        Assert.True(ScratchWorkspace.IsStale(
            new DirectoryInfo(directory),
            Now,
            ScratchWorkspace.DefaultStaleAfter,
            _ => false));
    }

    [Fact]
    public void LiveOwnerScratchIsNotStaleWhenYoung()
    {
        using var temp = new TempDir();
        var directory = CreateScratch(temp, "stratalint-c0-renew-beta", ownerPid: 4242);
        TouchNow(directory);

        Assert.False(ScratchWorkspace.IsStale(
            new DirectoryInfo(directory),
            Now,
            ScratchWorkspace.DefaultStaleAfter,
            pid => pid == 4242));
    }

    [Fact]
    public void YoungMarkerlessScratchIsNotStale()
    {
        using var temp = new TempDir();
        var directory = Path.Combine(temp.Path, "stratalint-conservative-gamma");
        Directory.CreateDirectory(directory);
        TouchNow(directory);

        Assert.False(ScratchWorkspace.IsStale(
            new DirectoryInfo(directory),
            Now,
            ScratchWorkspace.DefaultStaleAfter,
            _ => false));
    }

    [Fact]
    public void ScratchBeyondTtlIsStaleRegardlessOfOwnerLiveness()
    {
        using var temp = new TempDir();
        var directory = CreateScratch(temp, "stratalint-conservative-delta", ownerPid: 4242);
        Directory.SetLastWriteTimeUtc(directory, Now.UtcDateTime - TimeSpan.FromHours(25));

        Assert.True(ScratchWorkspace.IsStale(
            new DirectoryInfo(directory),
            Now,
            ScratchWorkspace.DefaultStaleAfter,
            _ => true));
    }

    [Fact]
    public void SweepRemovesStalePeersButKeepsActiveYoungAndUnrelated()
    {
        using var temp = new TempDir();
        var deadYoung = CreateScratch(temp, "stratalint-c0-renew-dead", ownerPid: 111);
        var liveYoung = CreateScratch(temp, "stratalint-conservative-live", ownerPid: 222);
        var markerlessYoung = Path.Combine(temp.Path, "stratalint-conservative-fresh");
        Directory.CreateDirectory(markerlessYoung);
        var overdue = CreateScratch(temp, "stratalint-c0-renew-overdue", ownerPid: 222);
        var unrelated = Path.Combine(temp.Path, "unrelated-keep-me");
        Directory.CreateDirectory(unrelated);
        foreach (var young in new[] { deadYoung, liveYoung, markerlessYoung, unrelated })
        {
            TouchNow(young);
        }

        Directory.SetLastWriteTimeUtc(overdue, Now.UtcDateTime - TimeSpan.FromHours(48));

        ScratchWorkspace.Sweep(
            [temp.Path],
            ScratchWorkspace.LegacyPrefixes,
            ScratchWorkspace.NoindexRootName,
            Now,
            ScratchWorkspace.DefaultStaleAfter,
            pid => pid == 222);

        Assert.False(Directory.Exists(deadYoung));
        Assert.False(Directory.Exists(overdue));
        Assert.True(Directory.Exists(liveYoung));
        Assert.True(Directory.Exists(markerlessYoung));
        Assert.True(Directory.Exists(unrelated));
    }

    [Fact]
    public void SweepReclaimsStaleChildrenOfNoindexRootWithoutDeletingTheRoot()
    {
        using var temp = new TempDir();
        var noindexRoot = Path.Combine(temp.Path, ScratchWorkspace.NoindexRootName);
        Directory.CreateDirectory(noindexRoot);
        var deadChild = CreateScratch(new TempDir(noindexRoot), "c0-renew-dead", ownerPid: 111);
        var liveChild = CreateScratch(new TempDir(noindexRoot), "c0-renew-live", ownerPid: 222);
        TouchNow(deadChild);
        TouchNow(liveChild);

        ScratchWorkspace.Sweep(
            [temp.Path],
            ScratchWorkspace.LegacyPrefixes,
            ScratchWorkspace.NoindexRootName,
            Now,
            ScratchWorkspace.DefaultStaleAfter,
            pid => pid == 222);

        Assert.True(Directory.Exists(noindexRoot));
        Assert.False(Directory.Exists(deadChild));
        Assert.True(Directory.Exists(liveChild));
    }

    [Fact]
    public void SweepIsIdempotentAndSafeOnMissingRoot()
    {
        using var temp = new TempDir();
        var stale = CreateScratch(temp, "stratalint-c0-renew-stale", ownerPid: 111);
        TouchNow(stale);

        void RunSweep() => ScratchWorkspace.Sweep(
            [temp.Path, Path.Combine(temp.Path, "does-not-exist")],
            ScratchWorkspace.LegacyPrefixes,
            ScratchWorkspace.NoindexRootName,
            Now,
            ScratchWorkspace.DefaultStaleAfter,
            _ => false);

        RunSweep();
        Assert.False(Directory.Exists(stale));
        RunSweep();
    }

    [Fact]
    public void ReserveCreatesOwnedDirectoryUnderNoindexRootWithCurrentProcessMarker()
    {
        var reserved = ScratchWorkspace.Reserve("c0-renew");
        try
        {
            Assert.StartsWith(
                Path.GetFullPath(ScratchWorkspace.NoindexRoot),
                Path.GetFullPath(reserved),
                StringComparison.Ordinal);
            Assert.StartsWith("c0-renew-", Path.GetFileName(reserved), StringComparison.Ordinal);
            Assert.True(Directory.Exists(reserved));

            var marker = Path.Combine(reserved, ScratchWorkspace.OwnerMarkerName);
            Assert.True(File.Exists(marker));
            Assert.Equal(
                Environment.ProcessId.ToString(CultureInfo.InvariantCulture),
                File.ReadAllText(marker).Trim());
        }
        finally
        {
            Directory.Delete(reserved, recursive: true);
        }
    }

    [Fact]
    public void MakeSweepBridgeRecipePinsCanonicalPrefixes()
    {
        // The phase-1 `make scratch-sweep` bridge is an inline TTL `find` over the legacy
        // flat leak dirs. Its prefixes must track the canonical ScratchWorkspace set so a
        // new ceremony prefix is swept there too, and it must use an age (`-mtime`) floor.
        var makefile = File.ReadAllText(Path.Combine(FindRepositoryRoot(), "Makefile"));

        Assert.Contains("-mtime", makefile, StringComparison.Ordinal);
        foreach (var prefix in ScratchWorkspace.LegacyPrefixes)
        {
            Assert.Contains(prefix, makefile, StringComparison.Ordinal);
        }
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

    private static DateTimeOffset Now => new(2026, 7, 23, 12, 0, 0, TimeSpan.Zero);

    private static string CreateScratch(TempDir temp, string name, int ownerPid)
    {
        var directory = Path.Combine(temp.Path, name);
        Directory.CreateDirectory(directory);
        File.WriteAllText(
            Path.Combine(directory, ScratchWorkspace.OwnerMarkerName),
            ownerPid.ToString(CultureInfo.InvariantCulture) + "\n",
            new UTF8Encoding(false));
        return directory;
    }

    private static void TouchNow(string directory) =>
        Directory.SetLastWriteTimeUtc(directory, Now.UtcDateTime - TimeSpan.FromMinutes(1));

    private sealed class TempDir : IDisposable
    {
        internal TempDir()
            : this(System.IO.Path.Combine(
                System.IO.Path.GetTempPath(),
                "stratalint-scratch-test-" + Guid.NewGuid().ToString("N")))
        {
        }

        internal TempDir(string path)
        {
            Path = path;
            Directory.CreateDirectory(path);
        }

        internal string Path { get; }

        public void Dispose()
        {
            try
            {
                if (Directory.Exists(Path)) Directory.Delete(Path, recursive: true);
            }
            catch (IOException)
            {
            }
        }
    }
}
