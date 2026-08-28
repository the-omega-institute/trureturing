using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class WorktreeCacheStrategyTests
{
    [Fact]
    public void RestoreRunsLockedAndFailureRollsBack()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "failed-restore");
        var runner = new RecordingWorktreeProcessRunner { FailDotnet = true };
        var branch = $"{WorktreeCommand.CreationNamespace}/math/failed-restore";

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--kind", "math",
                "--name", "failed-restore",
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
        AssertBranchMissing(repository.Path, branch);
    }

    [Fact]
    public void FailedWorktreeAddDoesNotCleanUpStateItDidNotCreate()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "concurrent-add");
        var runner = new RecordingWorktreeProcessRunner { FailWorktreeAdd = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--kind", "math",
                "--name", "concurrent-add",
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
        Git(repository.Path, "remote", "add", "origin", repository.Path);
        Git(repository.Path, "fetch", "origin");
        var target = Path.Combine(repository.Path, "fetched-default");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--kind", "math",
                "--name", "fetched-default",
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
    public void WorktreeToolingKeepsItsPathContractAndNeverWalksTheCacheTreePerFile()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));
        var init = File.ReadAllText(Path.Combine(root, "tools", "scripts", "worktree-init.sh"));
        var clean = File.ReadAllText(Path.Combine(root, "tools", "scripts", "clean-lanes.sh"));

        Assert.Contains("WORKTREE_DEST = $(if $(DEST)", makefile, StringComparison.Ordinal);
        Assert.Contains("[DEST=DIR]", makefile, StringComparison.Ordinal);
        Assert.Contains("\"$(KIND)\" \"$(NAME)\"", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("$(origin PATH)", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("BRANCH=", init, StringComparison.Ordinal);
        Assert.Contains("--kind \"$KIND\"", init, StringComparison.Ordinal);
        Assert.Contains("--name \"$NAME\"", init, StringComparison.Ordinal);
        Assert.Contains("exec dotnet run", init, StringComparison.Ordinal);
        Assert.DoesNotContain("case \"$KIND\" in", init, StringComparison.Ordinal);
        Assert.DoesNotContain("NAME must be", init, StringComparison.Ordinal);
        Assert.DoesNotContain("harness/$NAME", init, StringComparison.Ordinal);
        Assert.DoesNotContain("export PATH=", init, StringComparison.Ordinal);
        Assert.DoesNotContain("export PATH=", clean, StringComparison.Ordinal);

        // A per-file clone walk costs one system call per entry. Build the rejected forms
        // dynamically so the repository-wide guard does not match its own source.
        var cloneFlag = string.Concat('-', 'c');
        var recursiveFlag = string.Concat('-', 'R');
        var shellForm = $"cp {cloneFlag}";
        var argumentForm = $"\"{cloneFlag}\", \"{recursiveFlag}\"";
        var scan = TestProcessRunner.Run(
            "git",
            ["grep", "-n", "-I", "-e", shellForm, "-e", argumentForm, "--", "."],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);

        Assert.Equal(
            1,
            scan.ExitCode);
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

    private static string Git(string root, params string[] arguments) =>
        ReviewRegressionTests.RunGit(root, arguments);

    private static void AssertBranchMissing(string root, string branch)
    {
        var lookup = TestProcessRunner.Run(
            "git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{branch}"],
            root,
            BoundedProcessRunner.HangDetectionBudget,
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

    internal bool ThrowCopy { get; init; }

    internal string? LakeFileName { get; init; }

    internal bool FailLake { get; init; }

    internal bool ThrowCacheGetTimeout { get; init; }

    internal bool FailWrappedLake { get; init; }

    internal Action<string>? DuringWrappedLake { get; init; }

    internal bool FailClean { get; init; }

    internal bool ThrowClean { get; init; }

    internal bool OmitMathlibOleans { get; init; }

    internal bool FailDotnet { get; init; }

    internal bool FailWorktreeAdd { get; init; }

    internal bool BlockStampAfterCacheGet { get; init; }

    internal Action<string>? AfterWorktreeAdd { get; init; }

    internal string? BusyRoot { get; init; }

    internal bool BusyOnlyAfterCopy { get; init; }

    /// <summary>
    /// 归档取回的桩。默认**不拦**（返回 null），此时 ensure 会真去跑脚本；测试要观察
    /// 归档路径就设它。记录调用次数是为了钉住那条机器门：内容层不冷时**一次都不该调**。
    /// </summary>
    internal string? ArchiveReceipt { get; init; }

    internal int ArchiveInvocations { get; private set; }

    internal int ArchiveExitCode { get; init; }

    internal Action<string>? AfterArchiveFetch { get; init; }

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

        if (fileName == "cp" && arguments.FirstOrDefault() == "-R" && ThrowCopy)
        {
            throw new IOException("ordinary copy threw");
        }

        if (fileName == "/bin/bash"
            && arguments.Count >= 2
            && arguments[0].EndsWith("lean-cache-publish.sh", StringComparison.Ordinal)
            && arguments[1] == "fetch")
        {
            ArchiveInvocations++;
            // 成功的桩必须**真的落下产物**：只回一句 unpacked 而不造 olean，会让
            // 「成功后重探热度」这段代码删掉也不红 —— 那样它就只是生产代码，不是契约。
            AfterArchiveFetch?.Invoke(workingDirectory);
            return ArchiveReceipt is null
                ? Failure("archive fetcher is not stubbed for this test")
                : new ProcessOutput(ArchiveExitCode, Encoding.UTF8.GetBytes(ArchiveReceipt), []);
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
                if (ThrowCacheGetTimeout) throw new TimeoutException("cache get timed out");
                if (FailLake) return Failure("cache get failed");
                var lake = Path.Combine(workingDirectory, ".lake");
                Directory.CreateDirectory(lake);
                File.WriteAllText(Path.Combine(lake, "cache-get.marker"), "cache get\n");
                MathlibProjectionFixture.Write(lake, includeOleans: !OmitMathlibOleans);
                Directory.CreateDirectory(MathlibCacheFixture.CurrentPath);
                File.WriteAllText(Path.Combine(MathlibCacheFixture.CurrentPath, "current.ltar"), "current\n");
                if (BlockStampAfterCacheGet)
                {
                    Directory.CreateDirectory(LeanCacheStamp.PathFor(lake));
                }
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
                return Success();
            }

            DuringWrappedLake?.Invoke(workingDirectory);
            if (FailWrappedLake) return Failure("wrapped lake command failed");
            return Success();
        }

        if (fileName == "dotnet")
        {
            return FailDotnet ? Failure("dotnet restore failed") : Success();
        }

        var result = TestProcessRunner.Run(
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
