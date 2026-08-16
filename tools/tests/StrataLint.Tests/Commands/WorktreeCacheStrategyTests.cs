using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class WorktreeCacheStrategyTests
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
    public void MatchingDonorCanComeFromAnotherRegisteredWorktree()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var donor = Path.Combine(repository.Path, "registered-donor");
        Git(repository.Path, "worktree", "add", "-b", "harness/registered-donor", donor, "HEAD");
        WriteCache(donor, "registered donor cache\n");
        var target = Path.Combine(repository.Path, "from-registered-donor");

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/from-registered-donor",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        using var summary = JsonDocument.Parse(result.Output);
        var selectedDonor = Assert.IsType<string>(summary.RootElement.GetProperty("donor").GetString());
        Assert.Equal(Path.GetFileName(donor), Path.GetFileName(selectedDonor));
        Assert.True(Directory.Exists(selectedDonor));
        Assert.Equal(
            "registered donor cache\n",
            File.ReadAllText(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.True(LeanCacheStamp.Matches(Path.Combine(target, ".lake"), ReadPins(target), out _));
    }

    [Fact]
    public void BusyDonorIsSkippedAndCacheGetProducesTheOnlyQualifiedCache()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var donor = Path.Combine(repository.Path, "busy-donor");
        Git(repository.Path, "worktree", "add", "-b", "harness/busy-donor", donor, "HEAD");
        WriteCache(donor, "busy cache\n");
        var target = Path.Combine(repository.Path, "busy-target");
        using var busy = LeanCacheGuard.TryAcquireExclusive(Path.Combine(donor, ".lake"));
        Assert.NotNull(busy);
        using (var blocked = LeanCacheGuard.TryAcquireShared(Path.Combine(donor, ".lake")))
        {
            Assert.Null(blocked);
        }

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/busy-target",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        Assert.Contains("busy", result.Error, StringComparison.OrdinalIgnoreCase);
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
        var target = Path.Combine(repository.Path, "cwd-busy-target");
        var runner = new RecordingWorktreeProcessRunner { BusyRoot = repository.Path };
        Assert.True(LeanCacheBusyProbe.IsBusy(repository.Path, runner));
        using (var selection = GitWorktreeInventory.SelectDonor(repository.Path, ReadPins(repository.Path), runner))
        {
            Assert.Null(selection.Donor);
            Assert.Contains("busy", selection.Notice, StringComparison.OrdinalIgnoreCase);
        }

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/cwd-busy-target",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.True(
            result.Error.Contains("busy", StringComparison.OrdinalIgnoreCase),
            $"output={result.Output}; error={result.Error}");
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
        var target = Path.Combine(repository.Path, "post-copy-busy");
        var runner = new RecordingWorktreeProcessRunner
        {
            BusyRoot = repository.Path,
            BusyOnlyAfterCopy = true,
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/post-copy-busy",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
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
        var target = Path.Combine(repository.Path, "post-copy-stamp-change");
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = static (source, _) => File.Delete(LeanCacheStamp.PathFor(source)),
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/post-copy-stamp-change",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            runner,
            cloner);

        Assert.True(result.Success, result.Error);
        var clone = Assert.Single(cloner.Invocations);
        Assert.StartsWith(
            Path.Combine(target, ".lake.stage-"),
            clone.Target,
            StringComparison.Ordinal);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.Empty(Directory.EnumerateDirectories(target, ".lake.stage-*"));
        Assert.True(LeanCacheStamp.Matches(Path.Combine(target, ".lake"), ReadPins(target), out _));
    }

    [Fact]
    public void MismatchedPinsRefuseDonorAndRunCacheGet()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var baseRevision = Git(repository.Path, "rev-parse", "HEAD").Trim();
        File.WriteAllText(Path.Combine(repository.Path, "lean-toolchain"), "leanprover/lean4:v4.32.0\n");
        Git(repository.Path, "add", "lean-toolchain");
        Git(repository.Path, "commit", "-m", "change pins");
        WriteCache(repository.Path, "wrong donor cache\n");
        var target = Path.Combine(repository.Path, "pin-mismatch");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/pin-mismatch",
                "--path", target,
                "--base", baseRevision,
                "--skip-restore",
            ],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.Contains("\"donor\":null", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"cache_strategy\":\"cache-get\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("pin bytes", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Contains(
            runner.Invocations,
            static call => Path.GetFileName(call.FileName) == "lake"
                && call.Arguments.SequenceEqual(["exe", "cache", "get"]));
    }

    [Fact]
    public void ClonefileFailureFallsBackToIndependentOrdinaryCopy()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var donorFile = WriteCache(repository.Path, "warm cache\n");
        var target = Path.Combine(repository.Path, "copy-fallback");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/copy-fallback",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            runner,
            new RecordingDirectoryCloner
            {
                Results = new Queue<DirectoryCloneResult>(
                    [new(false, false, 17, 1, "clonefile unavailable")]),
            });

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"cache_strategy\":\"cloned\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"cache_method\":\"copy\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"clonefile_errno\":17", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"clonefile_errnos\":[17]", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"clonefile_attempts\":1", result.Output, StringComparison.Ordinal);
        Assert.Contains("clonefile unavailable", result.Error, StringComparison.Ordinal);
        File.WriteAllText(donorFile, "donor changed\n");
        Assert.Equal(
            "warm cache\n",
            File.ReadAllText(Path.Combine(target, ".lake", "build", "cache.bin")));
    }

    [Fact]
    public void RetrySuccessKeepsPriorErrnoInTheWorktreeReceipt()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm cache\n");
        var target = Path.Combine(repository.Path, "retry-success");
        var scripted = new Queue<DirectoryCloneResult>(
        [
            new(false, true, 5, 1, "clonefile(2) failed: EIO"),
            new(true, false, null, 1, null),
        ]);
        var cloner = new RecordingDirectoryCloner
        {
            Results = scripted,
            AfterClone = (_, path) =>
            {
                if (scripted.Count > 0) Directory.CreateDirectory(path);
            },
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/retry-success",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            new RecordingWorktreeProcessRunner(),
            cloner,
            wait: static _ => { });

        Assert.True(result.Success, result.Error);
        Assert.Equal(2, cloner.Invocations.Count);
        Assert.Contains("\"cache_method\":\"clonefile\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"clonefile_errno\":5", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"clonefile_errnos\":[5]", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"clonefile_attempts\":2", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void CacheGetFailureRollsBackWorktreeAndBranch()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var baseRevision = Git(repository.Path, "rev-parse", "HEAD").Trim();
        File.WriteAllText(Path.Combine(repository.Path, "lake-manifest.json"), "{\"version\": \"2.0.0\"}\n");
        Git(repository.Path, "add", "lake-manifest.json");
        Git(repository.Path, "commit", "-m", "change manifest");
        WriteCache(repository.Path, "wrong donor cache\n");
        var target = Path.Combine(repository.Path, "failed-cache-get");
        var runner = new RecordingWorktreeProcessRunner { FailLake = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/failed-cache-get",
                "--path", target,
                "--base", baseRevision,
                "--skip-restore",
            ],
            runner);

        Assert.False(result.Success);
        Assert.Contains("cache get failed", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.False(Directory.Exists(target));
        AssertBranchMissing(repository.Path, "harness/failed-cache-get");
    }

    [Fact]
    public void RestoreRunsLockedAndFailureRollsBack()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm cache\n");
        var target = Path.Combine(repository.Path, "failed-restore");
        var runner = new RecordingWorktreeProcessRunner { FailDotnet = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/failed-restore",
                "--path", target,
                "--base", "HEAD",
            ],
            runner);

        Assert.False(result.Success);
        Assert.Contains("dotnet restore failed", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Contains(
            runner.Invocations,
                static call => call.FileName == "dotnet"
                && call.Arguments.SequenceEqual(
                    ["restore", WorktreeCommand.SolutionPath, "--locked-mode"]));
        Assert.False(Directory.Exists(target));
        AssertBranchMissing(repository.Path, "harness/failed-restore");
    }

    [Fact]
    public void FailedWorktreeAddDoesNotCleanUpStateItDidNotCreate()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm cache\n");
        var target = Path.Combine(repository.Path, "concurrent-add");
        var runner = new RecordingWorktreeProcessRunner { FailWorktreeAdd = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/concurrent-add",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            runner);

        Assert.False(result.Success);
        Assert.Contains("simulated concurrent worktree", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "git"
                && call.Arguments.Take(2).SequenceEqual(["worktree", "remove"]));
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "git"
                && call.Arguments.Take(2).SequenceEqual(["branch", "-D"]));
    }

    [Fact]
    public void DefaultRemoteBaseFetchesBeforeAddingWorktree()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm cache\n");
        Git(repository.Path, "remote", "add", "origin", repository.Path);
        Git(repository.Path, "fetch", "origin");
        var target = Path.Combine(repository.Path, "fetched-default");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/fetched-default",
                "--path", target,
                "--skip-restore",
            ],
            runner);

        Assert.True(result.Success, result.Error);
        var fetchIndex = runner.Invocations.FindIndex(
            static call => call.FileName == "git" && call.Arguments.FirstOrDefault() == "fetch");
        var addIndex = runner.Invocations.FindIndex(
            static call => call.FileName == "git" && call.Arguments.Take(2).SequenceEqual(["worktree", "add"]));
        Assert.True(fetchIndex >= 0, "expected git fetch");
        Assert.True(addIndex > fetchIndex, "git fetch must precede git worktree add");
    }

    [Fact]
    public void LakeSymlinkIsRejectedAsDonor()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var realCache = Path.Combine(repository.Path, "real-cache");
        Directory.CreateDirectory(realCache);
        File.WriteAllText(Path.Combine(realCache, "cache.bin"), "shared cache\n");
        Directory.CreateSymbolicLink(Path.Combine(repository.Path, ".lake"), realCache);
        var target = Path.Combine(repository.Path, "symlink-donor");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/symlink-donor",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"cache_strategy\":\"cache-get\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("symlink", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.False(File.GetAttributes(Path.Combine(target, ".lake")).HasFlag(FileAttributes.ReparsePoint));
    }

    [Fact]
    public void WorktreeToolingKeepsItsPathContractAndNeverWalksTheCacheTreePerFile()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));
        var init = File.ReadAllText(Path.Combine(root, "tools", "scripts", "worktree-init.sh"));
        var clean = File.ReadAllText(Path.Combine(root, "tools", "scripts", "clean-lanes.sh"));

        Assert.Contains("WORKTREE_DEST = $(if $(DEST)", makefile, StringComparison.Ordinal);
        Assert.Contains("[DEST=DIR]", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("$(origin PATH)", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("export PATH=", init, StringComparison.Ordinal);
        Assert.DoesNotContain("export PATH=", clean, StringComparison.Ordinal);

        // A per-file clonefile walk over .lake costs one system call per entry: 197.5s
        // against 3.3s for the single directory-level clonefile(2). Assembled rather than
        // written out so this guard is not its own counterexample.
        var shellForm = "cp" + " -c";
        var argumentForm = "\"-c\"" + ", " + "\"-R\"";
        var scanned = Directory
            .EnumerateFiles(Path.Combine(root, "tools"), "*", SearchOption.AllDirectories)
            .Where(static path => !path.Contains($"{Path.DirectorySeparatorChar}bin{Path.DirectorySeparatorChar}", StringComparison.Ordinal))
            .Where(static path => !path.Contains($"{Path.DirectorySeparatorChar}obj{Path.DirectorySeparatorChar}", StringComparison.Ordinal))
            .Where(static path => Path.GetExtension(path) is ".cs" or ".sh" or ".yml" or ".yaml" or ".md")
            .Append(Path.Combine(root, "Makefile"))
            .Append(Path.Combine(root, "README.md"))
            .ToArray();
        Assert.NotEmpty(scanned);
        Assert.Empty(scanned
            .Where(path => File.ReadAllText(path) is var text
                && (text.Contains(shellForm, StringComparison.Ordinal)
                    || text.Contains(argumentForm, StringComparison.Ordinal)))
            .Select(path => Path.GetRelativePath(root, path))
            .ToArray());
    }

    private static void InitializeRepository(string root)
    {
        Git(root, "init", "--initial-branch=dev");
        Git(root, "config", "user.email", "stratalint@example.invalid");
        Git(root, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(Path.Combine(root, "README.md"), "# worktree fixture\n");
        File.WriteAllText(Path.Combine(root, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(root, "lake-manifest.json"), "{\"version\": \"1.1.0\"}\n");
        Git(root, "add", "README.md", "lean-toolchain", "lake-manifest.json");
        Git(root, "commit", "-m", "fixture baseline");
    }

    private static string WriteCache(string root, string contents)
    {
        var lake = Path.Combine(root, ".lake");
        var path = Path.Combine(lake, "build", "cache.bin");
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, contents);
        MathlibProjectionFixture.Write(lake);
        LeanCacheStamp.Write(lake, ReadPins(root));
        return path;
    }

    private static LeanPinSet ReadPins(string root) =>
        LeanPinSet.TryReadWorktree(root, out var reason)
        ?? throw new InvalidOperationException(reason);

    private static string Git(string root, params string[] arguments) =>
        ReviewRegressionTests.RunGit(root, arguments);

    private static void AssertBranchMissing(string root, string branch)
    {
        var lookup = BoundedProcessRunner.Run(
            "git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{branch}"],
            root,
            TimeSpan.FromSeconds(30),
            4096);
        Assert.Equal(1, lookup.ExitCode);
    }
}

internal sealed class RecordingDirectoryCloner : IDirectoryCloner
{
    internal List<(string Source, string Target)> Invocations { get; } = [];

    internal string? FailureReason { get; init; }

    internal Queue<DirectoryCloneResult> Results { get; init; } = [];

    internal Exception? ExceptionToThrow { get; init; }

    internal Action<string, string>? BeforeClone { get; init; }

    internal Action<string, string>? AfterClone { get; init; }

    public DirectoryCloneResult Clone(string source, string target)
    {
        Invocations.Add((source, target));
        if (ExceptionToThrow is not null) throw ExceptionToThrow;
        BeforeClone?.Invoke(source, target);
        var result = Results.Count > 0
            ? Results.Dequeue()
            : FailureReason is null
                ? new DirectoryCloneResult(true, false, null, 1, null)
                : new DirectoryCloneResult(false, false, null, 1, FailureReason);
        if (!result.Succeeded)
        {
            AfterClone?.Invoke(source, target);
            return result;
        }
        CopyTree(new DirectoryInfo(source), new DirectoryInfo(target));
        AfterClone?.Invoke(source, target);
        return result;
    }

    private static void CopyTree(DirectoryInfo source, DirectoryInfo target)
    {
        target.Create();
        foreach (var file in source.GetFiles())
        {
            file.CopyTo(Path.Combine(target.FullName, file.Name));
        }

        foreach (var directory in source.GetDirectories())
        {
            CopyTree(directory, new DirectoryInfo(Path.Combine(target.FullName, directory.Name)));
        }
    }
}

internal sealed record WorktreeProcessInvocation(
    string FileName,
    IReadOnlyList<string> Arguments,
    string WorkingDirectory,
    TimeSpan Timeout);

internal sealed class RecordingWorktreeProcessRunner : IWorktreeProcessRunner
{
    private bool copyCompleted;

    internal List<WorktreeProcessInvocation> Invocations { get; } = [];

    internal bool FailCopy { get; init; }

    internal string? LakeFileName { get; init; }

    internal bool FailLake { get; init; }

    internal bool FailClean { get; init; }

    internal bool ThrowClean { get; init; }

    internal bool OmitMathlibOleans { get; init; }

    internal bool FailDotnet { get; init; }

    internal bool FailWorktreeAdd { get; init; }

    internal bool BlockStampAfterClean { get; init; }

    internal Action<string>? AfterWorktreeAdd { get; init; }

    internal string? BusyRoot { get; init; }

    internal bool BusyOnlyAfterCopy { get; init; }

    internal bool CacheGetSawExistingProjection { get; private set; }

    internal List<bool> CacheGetExistingProjectionObservations { get; } = [];

    public ProcessOutput Run(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout)
    {
        Invocations.Add(new WorktreeProcessInvocation(
            fileName,
            arguments.ToArray(),
            workingDirectory,
            timeout));
        if (fileName == "git"
            && arguments.Take(2).SequenceEqual(["worktree", "add"])
            && FailWorktreeAdd)
        {
            return Failure("simulated concurrent worktree");
        }

        if (fileName == "cp" && arguments.FirstOrDefault() == "-R" && FailCopy)
        {
            return Failure("ordinary copy unavailable");
        }

        if (fileName == "lsof")
        {
            var busy = BusyRoot is not null && (!BusyOnlyAfterCopy || copyCompleted);
            return busy
                ? new ProcessOutput(0, Encoding.UTF8.GetBytes($"p123\nclean\nfcwd\nn{BusyRoot}\n"), [])
                : Success();
        }

        if ((LakeFileName is null && Path.GetFileName(fileName) == "lake")
            || fileName == LakeFileName)
        {
            if (arguments.SequenceEqual(["exe", "cache", "get"]))
            {
                var sawExistingProjection = File.Exists(
                    Path.Combine(workingDirectory, ".lake", "build", "cache.bin"));
                CacheGetSawExistingProjection |= sawExistingProjection;
                CacheGetExistingProjectionObservations.Add(sawExistingProjection);
                if (FailLake) return Failure("cache get failed");
                var lake = Path.Combine(workingDirectory, ".lake");
                Directory.CreateDirectory(lake);
                File.WriteAllText(Path.Combine(lake, "cache-get.marker"), "cache get\n");
                MathlibProjectionFixture.Write(lake, includeOleans: !OmitMathlibOleans);
                Directory.CreateDirectory(MathlibCacheFixture.CurrentPath);
                File.WriteAllText(Path.Combine(MathlibCacheFixture.CurrentPath, "current.ltar"), "current\n");
                return Success();
            }

            if (arguments.SequenceEqual(["exe", "cache", "clean"]))
            {
                if (ThrowClean) throw new IOException("cache clean threw");
                if (FailClean) return Failure("cache clean failed");
                foreach (var path in Directory.EnumerateFiles(MathlibCacheFixture.CurrentPath, "*.ltar"))
                {
                    if (Path.GetFileName(path) != "current.ltar") File.Delete(path);
                }
                if (BlockStampAfterClean)
                {
                    Directory.CreateDirectory(LeanCacheStamp.PathFor(Path.Combine(workingDirectory, ".lake")));
                }
                return Success();
            }

            return Success();
        }

        if (fileName == "dotnet")
        {
            return FailDotnet ? Failure("dotnet restore failed") : Success();
        }

        var result = BoundedProcessRunner.Run(
            fileName,
            arguments,
            workingDirectory,
            timeout,
            64 * 1024 * 1024);
        if (fileName == "git"
            && arguments.Take(2).SequenceEqual(["worktree", "add"])
            && result.ExitCode == 0)
        {
            AfterWorktreeAdd?.Invoke(arguments[4]);
        }
        if (fileName == "cp" && result.ExitCode == 0) copyCompleted = true;
        return result;
    }

    private static ProcessOutput Success() => new(0, [], []);

    private static ProcessOutput Failure(string message) =>
        new(1, [], Encoding.UTF8.GetBytes(message));
}

internal static class MathlibProjectionFixture
{
    private static readonly string[] Modules =
    [
        "Mathlib/Algebra/Basic",
        "Mathlib/Topology/Basic",
    ];

    internal static int ModuleCount => Modules.Length;

    internal static string FirstModule => Modules[0];

    internal static void Write(string lake, bool includeOleans = true)
    {
        var mathlib = Path.Combine(lake, "packages", "mathlib");
        foreach (var module in Modules)
        {
            var relative = module.Replace('/', Path.DirectorySeparatorChar);
            var source = Path.Combine(mathlib, relative + ".lean");
            Directory.CreateDirectory(Path.GetDirectoryName(source)!);
            File.WriteAllText(source, "-- fixture\n");
            if (!includeOleans) continue;

            var olean = Path.Combine(mathlib, ".lake", "build", "lib", "lean", relative + ".olean");
            Directory.CreateDirectory(Path.GetDirectoryName(olean)!);
            File.WriteAllText(olean, "fixture\n");
        }
    }

    internal static void RemoveAllOleans(string lake)
    {
        var buildRoot = Path.Combine(
            lake,
            "packages",
            "mathlib",
            ".lake",
            "build",
            "lib",
            "lean");
        foreach (var olean in Directory.EnumerateFiles(
            buildRoot,
            "*.olean",
            SearchOption.AllDirectories))
        {
            File.Delete(olean);
        }
    }
}

internal sealed class MathlibCacheFixture : IDisposable
{
    private readonly TemporaryDirectory temporary = new();
    private readonly string? previous = Environment.GetEnvironmentVariable("MATHLIB_CACHE_DIR");

    internal MathlibCacheFixture()
    {
        Environment.SetEnvironmentVariable("MATHLIB_CACHE_DIR", temporary.Path);
        File.WriteAllText(Path.Combine(temporary.Path, "old.ltar"), "old\n");
    }

    internal static string CurrentPath =>
        Environment.GetEnvironmentVariable("MATHLIB_CACHE_DIR")
        ?? throw new InvalidOperationException("MATHLIB_CACHE_DIR is not set for the cache test");

    public void Dispose()
    {
        Environment.SetEnvironmentVariable("MATHLIB_CACHE_DIR", previous);
        temporary.Dispose();
    }
}
