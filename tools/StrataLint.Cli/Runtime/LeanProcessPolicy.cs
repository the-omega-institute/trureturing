using System.Collections;
using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Cli;

// Lake owns artifact hashes, publication, and resolved paths. This boundary only
// pins the child environment and coordinates mutations to this checkout's .lake.
internal sealed class LeanProcessPolicy : IWorktreeProcessRunner
{
    private readonly IWorktreeProcessRunner runner;
    private readonly Dictionary<string, string> environment;
    internal string Root { get; }
    internal string LockDirectory { get; }
    internal string LakeExecutable { get; }
    internal IReadOnlyList<LeanCacheWriterGuard> Writers { get; set; } = [];

    private LeanProcessPolicy(string root, string lockDirectory, string lakeExecutable,
        IWorktreeProcessRunner runner, Dictionary<string, string> environment)
    {
        Root = root;
        LockDirectory = lockDirectory;
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
        child["LAKE_BIN"] = lake;
        child["LAKE_ARTIFACT_CACHE"] = "true";
        // Restore module-shaped outputs for local and CI consumers alike. Lake
        // shares immutable artifacts; each checkout keeps its own mutable state.
        child["LAKE_RESTORE_ARTIFACTS"] = "true";
        // Disable automatic package archive bootstrap, not the native artifact cache.
        // Explicit package restoreAllArtifacts settings (including Mathlib's) win.
        child["LAKE_NO_CACHE"] = "true";
        child["MATHLIB_NO_CACHE_ON_UPDATE"] = "1";
        child["MATHLIB_CACHE_DIR"] = Path.Combine(root, ".lake", "mathlib-cache");
        var common = Git(root, runner, "rev-parse", "--path-format=absolute", "--git-common-dir");
        var policy = new LeanProcessPolicy(root,
            Path.Combine(LeanCacheGuard.PhysicalPath(common), "stratalint-lake-locks"), lake, runner, child);
        var check = policy.Run(lake, ["--version"], root, BoundedProcessRunner.HangDetectionBudget);
        if (check.ExitCode != 0 || !Encoding.UTF8.GetString(check.StandardOutput)
            .Contains("(Lean version " + version.Groups[1].Value + ")", StringComparison.Ordinal))
            throw new InvalidOperationException("Lake executable does not match lean-toolchain: " + lake);
        return policy;
    }

    public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments,
        string workingDirectory, TimeSpan timeout)
    {
        if (Path.GetFileName(fileName) == "lake") fileName = LakeExecutable;
        return LeanCacheProcessLifetime.Run(runner, fileName, arguments, workingDirectory,
            timeout, environment, Writers);
    }

    internal static string Git(string root, IWorktreeProcessRunner runner, params string[] arguments)
    {
        var result = RunGit(root, runner, arguments);
        if (result.ExitCode != 0)
            throw new InvalidOperationException("git " + arguments[0] + ": " + Encoding.UTF8.GetString(result.StandardError));
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    internal static ProcessOutput RunGit(string root, IWorktreeProcessRunner runner,
        IReadOnlyList<string> arguments) => runner is LeanProcessPolicy policy
            ? policy.Run("git", arguments, root, BoundedProcessRunner.HangDetectionBudget)
            : runner.RunWithEnvironment("git", arguments, root,
                BoundedProcessRunner.HangDetectionBudget, PhysicalGitEnvironment());

    private static Dictionary<string, string> PhysicalGitEnvironment()
    {
        var child = Environment.GetEnvironmentVariables().Cast<DictionaryEntry>()
            .ToDictionary(entry => (string)entry.Key, entry => (string)entry.Value!, StringComparer.Ordinal);
        // Git's repository-local variables (git rev-parse --local-env-vars), plus discovery
        // and config-selection overrides. Disable diagnostic destinations before bootstrap
        // discovery can write them. Trace2 ignores -c and repository-local config;
        // explicit environment zeros override its system/global configuration.
        // Transport, credentials and optional locks remain the caller's environment.
        // The same context reaches Lake's child Git calls.
        foreach (var name in child.Keys.Where(name => name.StartsWith("GIT_CONFIG_", StringComparison.Ordinal)
            || name.StartsWith("GIT_TRACE", StringComparison.Ordinal)
            || name is "GIT_ALTERNATE_OBJECT_DIRECTORIES" or "GIT_CONFIG" or "GIT_OBJECT_DIRECTORY"
                or "GIT_DIR" or "GIT_WORK_TREE" or "GIT_IMPLICIT_WORK_TREE" or "GIT_GRAFT_FILE"
                or "GIT_INDEX_FILE" or "GIT_NO_REPLACE_OBJECTS" or "GIT_REPLACE_REF_BASE"
                or "GIT_PREFIX" or "GIT_SHALLOW_FILE" or "GIT_COMMON_DIR"
                or "GIT_CEILING_DIRECTORIES" or "GIT_DISCOVERY_ACROSS_FILESYSTEM").ToArray())
            child.Remove(name);
        child["GIT_TRACE2"] = "0";
        child["GIT_TRACE2_EVENT"] = "0";
        child["GIT_TRACE2_PERF"] = "0";
        return child;
    }

}
