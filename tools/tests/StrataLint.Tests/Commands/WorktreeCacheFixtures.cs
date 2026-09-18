using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// Worktree 缓存测试共用的进程与目录复制夹具。

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

internal static class WorktreeHookFixture
{
    internal static string Install(string repository, string name, string body)
    {
        var hooks = Path.Combine(repository, ".git", "creation-hooks");
        Directory.CreateDirectory(hooks);
        RunGit(repository, "config", "core.hooksPath", hooks);
        var path = Path.Combine(hooks, name);
        File.WriteAllText(path, "#!/bin/sh\nset -eu\n" + body, new UTF8Encoding(false));
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        return path;
    }

    internal static string RunGit(string repository, params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, repository,
            BoundedProcessRunner.HangDetectionBudget, 64 * 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        return Encoding.UTF8.GetString(result.StandardOutput);
    }
}

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
    /// 归档 fetch 的桩输出,调用次数由 ArchiveInvocations 记录。
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
            // 成功场景通过回调写入产物,供后续热度探测读取。
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
            AfterWorktreeAdd?.Invoke(arguments[^2]);
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
