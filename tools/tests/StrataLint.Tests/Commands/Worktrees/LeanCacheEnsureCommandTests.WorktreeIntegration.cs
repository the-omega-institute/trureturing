using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// LeanCacheEnsureCommandTests 的 worktree 集成片段。它此前寄居在
// Commands/WorktreeCommandTests.cs —— 一个以**另一个测试类**命名的文件里,
// 而该类的正宗归宿是 Commands/Worktrees/。
// 搬迁同时给宿主买回余量:796 行(离 800 硬线仅 4 行)→ 548 行。

public sealed partial class LeanCacheEnsureCommandTests
{
    [Fact]
    public void DonorGuardsAreSharedWhileCanonicalWriterGuardIsExclusive()
    {
        using var root = new TemporaryDirectory();
        var lake = Path.Combine(root.Path, ".lake");
        using var first = LeanCacheGuard.TryAcquireShared(lake);
        using var second = LeanCacheGuard.TryAcquireShared(lake);

        Assert.NotNull(first);
        Assert.NotNull(second);
        using var writer = LeanCacheGuard.TryAcquireExclusive(lake);
        Assert.Null(writer);
    }

    [Fact]
    public void BusyTargetWriterFailsClosedBeforeEnsuring()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = AddWorktree(repository.Path, "busy-writer-target");
        var runner = new RecordingWorktreeProcessRunner();
        using var busy = LeanCacheWriterGuard.TryAcquire(Path.Combine(target, ".lake"));
        Assert.NotNull(busy);

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner);

        Assert.False(result.Success);
        Assert.Contains("busy", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Empty(runner.Invocations);
    }

    [Fact]
    public void EnsureHoldsTargetWriterGuardThroughoutProvisioning()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "guarded donor cache\n");
        var target = AddWorktree(repository.Path, "guarded-target");
        bool? concurrentWriterAcquired = null;
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) =>
            {
                using var concurrent = LeanCacheWriterGuard.TryAcquire(Path.Combine(target, ".lake"));
                concurrentWriterAcquired = concurrent is not null;
            },
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.False(concurrentWriterAcquired);
    }

    [Fact]
    public void BusyDonorIsSkippedAndEnsureUsesCacheGet()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var donor = AddWorktree(repository.Path, "busy-donor");
        WriteCache(donor, "busy cache\n");
        var target = AddWorktree(repository.Path, "busy-target");
        using var busy = LeanCacheGuard.TryAcquireExclusive(Path.Combine(donor, ".lake"));
        Assert.NotNull(busy);

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        Assert.Contains("busy", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
    }

    [Fact]
    public void CwdBusyProbeSkipsDonorWithoutTreatingTheProbeAsProof()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "busy cache\n");
        var target = AddWorktree(repository.Path, "cwd-busy-target");
        var runner = new RecordingWorktreeProcessRunner { BusyRoot = repository.Path };
        Assert.True(LeanCacheBusyProbe.IsBusy(repository.Path, runner));

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.Contains("busy", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.DoesNotContain(runner.Invocations, static call => call.FileName == "cp");
    }

    [Fact]
    public void DonorBecomingBusyAfterStagingFallsBackWithoutPublishingTheCopy()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "copy raced cache\n");
        var target = AddWorktree(repository.Path, "post-copy-busy");
        var runner = new RecordingWorktreeProcessRunner
        {
            BusyRoot = repository.Path,
            BusyOnlyAfterCopy = true,
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            new RecordingDirectoryCloner { FailureReason = "clonefile unavailable" });

        Assert.True(result.Success, result.Error);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.Empty(Directory.EnumerateDirectories(target, ".lake.stage-*"));
        Assert.True(LeanCacheStamp.Matches(Path.Combine(target, ".lake"), ReadPins(target), out _));
    }

    [Fact]
    public void DonorStampChangingAfterStagingFallsBackWithoutPublishingTheCopy()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "copy raced stamp\n");
        var target = AddWorktree(repository.Path, "post-copy-stamp-change");
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = static (source, _) => File.Delete(LeanCacheStamp.PathFor(source)),
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Single(cloner.Invocations);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.Empty(Directory.EnumerateDirectories(target, ".lake.stage-*"));
        Assert.True(LeanCacheStamp.Matches(Path.Combine(target, ".lake"), ReadPins(target), out _));
    }

    [Fact]
    public void LakeSymlinkIsRejectedAsDonor()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var realCache = Path.Combine(repository.Path, "real-cache");
        Directory.CreateDirectory(realCache);
        Directory.CreateSymbolicLink(Path.Combine(repository.Path, ".lake"), realCache);
        var target = AddWorktree(repository.Path, "symlink-donor-target");

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        Assert.Contains("symlink", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.GetAttributes(Path.Combine(target, ".lake")).HasFlag(FileAttributes.ReparsePoint));
    }

    [Fact]
    public void ClonefileCleanupFailureReceiptSerializesInjectedError()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "cleanup failure donor cache\n");
        var target = AddWorktree(repository.Path, "cleanup-failure-target");
        var cloner = new RecordingDirectoryCloner
        {
            Results = new Queue<DirectoryCloneResult>(
                [new(false, true, 5, 1, "clonefile(2) failed: EIO")]),
            AfterClone = (_, path) => Directory.CreateDirectory(path),
        };
        var cleanupCalls = 0;
        void Cleanup(string path)
        {
            cleanupCalls++;
            if (cleanupCalls == 1) throw new IOException("injected clone retry cleanup failure");
            if (Directory.Exists(path)) Directory.Delete(path, recursive: true);
        }
        var runner = new RecordingWorktreeProcessRunner();

        var result = LeanCacheEnsureCommand.Run(
            repository.Path,
            ["--path", target],
            runner,
            cloner,
            Cleanup);

        Assert.True(result.Success, result.Error);
        Assert.Empty(result.Error);
        Assert.Equal(2, cleanupCalls);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(
            "injected clone retry cleanup failure",
            receipt.RootElement.GetProperty("clonefile_cleanup_error").GetString());
    }
}
