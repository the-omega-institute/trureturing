using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class WorktreeCacheStrategyTests
{
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
    }

    [Fact]
    public void MismatchedPinsRefuseDonorAndRunCacheGet()
    {
        using var repository = new TemporaryDirectory();
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
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["exe", "cache", "get"]));
    }

    [Fact]
    public void ClonefileFailureFallsBackToIndependentOrdinaryCopy()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var donorFile = WriteCache(repository.Path, "warm cache\n");
        var target = Path.Combine(repository.Path, "copy-fallback");
        var runner = new RecordingWorktreeProcessRunner { FailClonefile = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/copy-fallback",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"cache_strategy\":\"cloned\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"cache_method\":\"copy\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("clonefile unavailable", result.Error, StringComparison.Ordinal);
        File.WriteAllText(donorFile, "donor changed\n");
        Assert.Equal(
            "warm cache\n",
            File.ReadAllText(Path.Combine(target, ".lake", "build", "cache.bin")));
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
        var path = Path.Combine(root, ".lake", "build", "cache.bin");
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, contents);
        return path;
    }

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

internal sealed record WorktreeProcessInvocation(
    string FileName,
    IReadOnlyList<string> Arguments,
    string WorkingDirectory,
    TimeSpan Timeout);

internal sealed class RecordingWorktreeProcessRunner : IWorktreeProcessRunner
{
    internal List<WorktreeProcessInvocation> Invocations { get; } = [];

    internal bool FailClonefile { get; init; }

    internal bool FailCopy { get; init; }

    internal bool FailLake { get; init; }

    internal bool FailDotnet { get; init; }

    internal bool FailWorktreeAdd { get; init; }

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

        if (fileName == "cp" && arguments.FirstOrDefault() == "-c" && FailClonefile)
        {
            return Failure("clonefile unavailable");
        }

        if (fileName == "cp" && arguments.FirstOrDefault() == "-R" && FailCopy)
        {
            return Failure("ordinary copy unavailable");
        }

        if (fileName == "lake")
        {
            if (FailLake) return Failure("cache get failed");
            var lake = Path.Combine(workingDirectory, ".lake");
            Directory.CreateDirectory(lake);
            File.WriteAllText(Path.Combine(lake, "cache-get.marker"), "cache get\n");
            return Success();
        }

        if (fileName == "dotnet")
        {
            return FailDotnet ? Failure("dotnet restore failed") : Success();
        }

        return BoundedProcessRunner.Run(
            fileName,
            arguments,
            workingDirectory,
            timeout,
            64 * 1024 * 1024);
    }

    private static ProcessOutput Success() => new(0, [], []);

    private static ProcessOutput Failure(string message) =>
        new(1, [], Encoding.UTF8.GetBytes(message));
}
