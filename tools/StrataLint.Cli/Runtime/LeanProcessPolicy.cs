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
    internal string Cache { get; }
    internal string LakeExecutable { get; }
    internal bool SharedReader => Cache == SharedCache;

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
        var child = Environment.GetEnvironmentVariables().Cast<DictionaryEntry>()
            .ToDictionary(entry => (string)entry.Key, entry => (string)entry.Value!, StringComparer.Ordinal);
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
        return new(Root, SharedRoot, SharedCache, stage, LakeExecutable, runner, child);
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
                    LakeExecutable, runner, child).RunOnce(fileName, arguments, workingDirectory, timeout);
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
        if (OperatingSystem.IsMacOS() && File.Exists("/usr/bin/sandbox-exec"))
        {
            var literal = SharedRoot.Replace("\\", "\\\\", StringComparison.Ordinal)
                .Replace("\"", "\\\"", StringComparison.Ordinal);
            var profile = "(version 1) (allow default) (deny file-write* (subpath \"" + literal + "\"))";
            return runner.RunWithEnvironment("/usr/bin/sandbox-exec",
                ["-p", profile, fileName, .. arguments], workingDirectory, timeout, environment);
        }
        return runner.RunWithEnvironment(fileName, arguments, workingDirectory, timeout, environment);
    }

    internal static string Git(string root, IWorktreeProcessRunner runner, params string[] arguments)
    {
        var result = runner.Run("git", arguments, root, BoundedProcessRunner.HangDetectionBudget);
        if (result.ExitCode != 0)
            throw new InvalidOperationException("git " + arguments[0] + ": " + Encoding.UTF8.GetString(result.StandardError));
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }
}
