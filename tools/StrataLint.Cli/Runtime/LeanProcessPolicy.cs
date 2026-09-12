using System.Collections;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class LeanProcessPolicy : IWorktreeProcessRunner
{
    private readonly IWorktreeProcessRunner runner;
    private readonly Dictionary<string, string> environment;
    internal string Root { get; }
    internal string SharedRoot { get; }
    internal string SharedCache { get; }
    internal string LockDirectory => Path.Combine(Path.GetDirectoryName(SharedRoot)!, "stratalint-lake-locks");
    internal string Cache { get; }
    internal string LakeExecutable { get; }
    internal bool SharedReader => Cache == SharedCache;
    internal IReadOnlyList<LeanCacheWriterGuard> Writers { get; set; } = [];

    private LeanProcessPolicy(string root, string sharedRoot, string sharedCache,
        string cache, string lakeExecutable, IWorktreeProcessRunner runner,
        Dictionary<string, string> environment)
    {
        Root = root;
        SharedRoot = sharedRoot;
        SharedCache = sharedCache;
        Cache = cache;
        LakeExecutable = lakeExecutable;
        this.runner = runner;
        this.environment = environment;
    }

    internal static LeanProcessPolicy Create(string root, LeanPinSet pins, IWorktreeProcessRunner runner)
    {
        root = LeanCacheGuard.PhysicalPath(root);
        var toolchain = Encoding.UTF8.GetString(pins.LeanToolchain).Trim();
        var version = Regex.Match(toolchain, @"^leanprover/lean4:v(\d+\.\d+\.\d+(?:-[a-zA-Z0-9.]+)?)$");
        if (!version.Success) throw new InvalidOperationException("Expected a pinned Lean release in lean-toolchain.");
        if (!LeanLakeExecutable.TryResolve(out var lake, out var reason))
            throw new InvalidOperationException(reason);
        var child = PhysicalGitEnvironment();
        foreach (var name in child.Keys.Where(name => name.StartsWith("LAKE_", StringComparison.Ordinal)
            || name is "LEAN_PATH" or "LEAN_SRC_PATH" or "LEAN_SYSROOT" or "LEAN" or "LEAN_GITHASH"
                or "ELAN_TOOLCHAIN" or "ELAN_HOME" or "MATHLIB_CACHE_DIR").ToArray())
            child.Remove(name);
        child["ELAN_TOOLCHAIN"] = toolchain;
        child["LAKE_CONFIG"] = Path.Combine(root, ".lake", "config.toml");
        child["LAKE_RESTORE_ARTIFACTS"] = "true";
        child["MATHLIB_CACHE_DIR"] = Path.Combine(root, ".lake", "mathlib-cache");
        var check = runner.RunWithEnvironment(lake, ["--version"], root,
            BoundedProcessRunner.HangDetectionBudget, child);
        if (check.ExitCode != 0 || !Encoding.UTF8.GetString(check.StandardOutput)
            .Contains("(Lean version " + version.Groups[1].Value + ")", StringComparison.Ordinal))
            throw new InvalidOperationException("Lake executable does not match lean-toolchain: " + lake);
        var common = Git(root, runner, "rev-parse", "--path-format=absolute", "--git-common-dir");
        var sharedRoot = LeanCacheGuard.PhysicalPath(Path.Combine(common, "stratalint-lake"));
        if (sharedRoot != Path.Combine(LeanCacheGuard.PhysicalPath(common), "stratalint-lake"))
            throw new InvalidOperationException("Shared cache must reside below the canonical git-common-dir.");
        var platform = (OperatingSystem.IsMacOS() ? "macos" : OperatingSystem.IsLinux() ? "linux" : "windows")
            + "-" + RuntimeInformation.ProcessArchitecture.ToString().ToLowerInvariant();
        var sharedCache = Path.Combine(sharedRoot, "lean-" + version.Groups[1].Value, platform);
        foreach (var path in new[] { Path.GetDirectoryName(sharedCache)!, sharedCache })
            if (new DirectoryInfo(path).LinkTarget is not null)
                throw new InvalidOperationException("Shared cache partitions must not be symlinks.");
        RequireGuard(sharedRoot);
        var cache = Directory.Exists(sharedCache) ? sharedCache : Path.Combine(root, ".lake", "artifact-cache");
        child["LAKE_CACHE_DIR"] = cache;
        return new(root, sharedRoot, sharedCache, cache, lake, runner, child);
    }

    internal LeanProcessPolicy StageWriter(string stage)
    {
        var child = new Dictionary<string, string>(environment)
        {
            ["LAKE_CACHE_DIR"] = stage,
            ["LAKE_ARTIFACT_CACHE"] = "true",
            ["LAKE_NO_CACHE"] = "true",
        };
        return new(Root, SharedRoot, SharedCache, stage, LakeExecutable, runner, child) { Writers = Writers };
    }

    internal static void RequireGuard(string sharedRoot)
    {
        if (OperatingSystem.IsMacOS() && File.Exists("/usr/bin/sandbox-exec")) return;
        if (Directory.Exists(sharedRoot))
            throw new PlatformNotSupportedException("Shared Lake cache requires a verified read-only process guard; "
                + "only macOS sandbox-exec is supported. This platform can use private caches when no shared store exists.");
    }

    public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments,
        string workingDirectory, TimeSpan timeout)
    {
        if (Path.GetFileName(fileName) == "lake") fileName = LakeExecutable;
        var result = RunOnce(fileName, arguments, workingDirectory, timeout);
        if (SharedReader && fileName == LakeExecutable && arguments.FirstOrDefault() == "build"
            && result.ExitCode != 0)
        {
            var diagnostic = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
            if (diagnostic.Contains("operation not permitted (error code: 1)", StringComparison.Ordinal)
                && diagnostic.Contains("file: " + SharedCache + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            {
                var privateCache = Path.Combine(Root, ".lake", "artifact-cache");
                var child = new Dictionary<string, string>(environment) { ["LAKE_CACHE_DIR"] = privateCache };
                var local = new LeanProcessPolicy(Root, SharedRoot, SharedCache, privateCache,
                    LakeExecutable, runner, child) { Writers = Writers }.RunOnce(fileName, arguments, workingDirectory, timeout);
                var output = "LEAN_CACHE_FALLBACK denied shared cache write; retrying Lake build with private cache\n"
                    + diagnostic + Encoding.UTF8.GetString(local.StandardOutput);
                return new(local.ExitCode, Encoding.UTF8.GetBytes(output), local.StandardError);
            }
        }
        return result;
    }

    private ProcessOutput RunOnce(string fileName, IReadOnlyList<string> arguments,
        string workingDirectory, TimeSpan timeout)
    {
        RequireGuard(SharedRoot);
        foreach (var ancestor in new[] { SharedRoot, Path.GetDirectoryName(SharedCache)! })
            if (new DirectoryInfo(ancestor).LinkTarget is not null)
                throw new InvalidOperationException("Shared cache ancestors must not be symlinks: " + ancestor);
        RequireNoSharedLinks(SharedCache);
        if (OperatingSystem.IsMacOS() && File.Exists("/usr/bin/sandbox-exec"))
        {
            var literal = SharedRoot.Replace("\\", "\\\\", StringComparison.Ordinal)
                .Replace("\"", "\\\"", StringComparison.Ordinal);
            var profile = "(version 1) (allow default) (deny file-write* (subpath \"" + literal + "\"))";
            return LeanCacheProcessLifetime.Run(runner, "/usr/bin/sandbox-exec",
                ["-p", profile, fileName, .. arguments], workingDirectory, timeout, environment, Writers);
        }
        return LeanCacheProcessLifetime.Run(runner, fileName, arguments, workingDirectory, timeout, environment, Writers);
    }

    internal static string Git(string root, IWorktreeProcessRunner runner, params string[] arguments)
    {
        var result = runner is LeanProcessPolicy policy
            ? policy.Run("git", arguments, root, BoundedProcessRunner.HangDetectionBudget)
            : runner.RunWithEnvironment("git", arguments, root, BoundedProcessRunner.HangDetectionBudget,
                PhysicalGitEnvironment());
        if (result.ExitCode != 0)
            throw new InvalidOperationException("git " + arguments[0] + ": " + Encoding.UTF8.GetString(result.StandardError));
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static Dictionary<string, string> PhysicalGitEnvironment()
    {
        var child = Environment.GetEnvironmentVariables().Cast<DictionaryEntry>()
            .ToDictionary(entry => (string)entry.Key, entry => (string)entry.Value!, StringComparer.Ordinal);
        // Git's repository-local variables (git rev-parse --local-env-vars), plus discovery
        // and config-selection overrides. Transport, credentials, tracing and optional locks
        // remain the caller's environment. The same context reaches Lake's child Git calls.
        foreach (var name in child.Keys.Where(name => name.StartsWith("GIT_CONFIG_", StringComparison.Ordinal)
            || name is "GIT_ALTERNATE_OBJECT_DIRECTORIES" or "GIT_CONFIG" or "GIT_OBJECT_DIRECTORY"
                or "GIT_DIR" or "GIT_WORK_TREE" or "GIT_IMPLICIT_WORK_TREE" or "GIT_GRAFT_FILE"
                or "GIT_INDEX_FILE" or "GIT_NO_REPLACE_OBJECTS" or "GIT_REPLACE_REF_BASE"
                or "GIT_PREFIX" or "GIT_SHALLOW_FILE" or "GIT_COMMON_DIR"
                or "GIT_CEILING_DIRECTORIES" or "GIT_DISCOVERY_ACROSS_FILESYSTEM").ToArray())
            child.Remove(name);
        return child;
    }

    internal static void RequireNoSharedLinks(string path)
    {
        var directory = new DirectoryInfo(path);
        if (directory.LinkTarget is not null)
            throw new InvalidOperationException("Shared cache entries must not be symlinks: " + path);
        if (!directory.Exists) return;
        foreach (var item in directory.EnumerateFileSystemInfos())
        {
            if ((item.Attributes & FileAttributes.ReparsePoint) != 0)
                throw new InvalidOperationException("Shared cache entries must not be symlinks: " + item.FullName);
            if (item is DirectoryInfo) RequireNoSharedLinks(item.FullName);
        }
    }
}
