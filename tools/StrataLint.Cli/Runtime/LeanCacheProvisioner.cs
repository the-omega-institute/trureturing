using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class LeanCacheProvisioner
{
    internal const int MinProvisionBudgetSeconds = LeanCacheBudgetPolicy.MinimumConfigurableBudgetSeconds;
    internal const int MaxProvisionBudgetSeconds = LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds;

    internal static TimeSpan ProvisionBudgetFor()
    {
        var raw = Environment.GetEnvironmentVariable("STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS");
        return TimeSpan.FromSeconds(int.TryParse(raw, System.Globalization.NumberStyles.Integer,
            System.Globalization.CultureInfo.InvariantCulture, out var seconds)
                ? Math.Clamp(seconds, MinProvisionBudgetSeconds, MaxProvisionBudgetSeconds)
                : MaxProvisionBudgetSeconds);
    }

    internal static TimeSpan LeanCommandBudget => ProvisionBudgetFor();
    internal static TimeSpan DependencyFetchBudget => LeanCommandBudget;

    internal static string Ensure(LeanProcessPolicy policy, LeanPinSet pins, LeanCacheWriterGuard guard)
    {
        var root = policy.Root;
        var lake = Path.Combine(root, ".lake");
        guard.RequireOwnershipOf(lake);
        RequirePrivateLake(root);
        Directory.CreateDirectory(lake);
        var stamp = LeanCacheStamp.Inspect(lake, pins);
        // The durable stamp records pins, not current source availability. Native Lake
        // validates/materializes the pinned Git dependencies on every standalone ensure.
        var dependencies = policy.Run(policy.LakeExecutable,
            ["env"],
            root, DependencyFetchBudget);
        RequireSuccess(dependencies, "Lake dependency materialization");
        var cacheLine = Encoding.UTF8.GetString(dependencies.StandardOutput).Split('\n')
            .SingleOrDefault(line => line.StartsWith("LAKE_CACHE_DIR=", StringComparison.Ordinal));
        var cache = cacheLine?["LAKE_CACHE_DIR=".Length..].TrimEnd('\r');
        if (string.IsNullOrEmpty(cache))
            throw new InvalidOperationException("Lake did not resolve an artifact cache directory.");
        if (stamp.State != LeanCacheStampState.Match) LeanCacheStamp.Write(lake, pins);
        return "LEAN_CACHE " + JsonSerializer.Serialize(new
        {
            status = "ready", worktree = root, mode = "official-writable",
            cache,
        }) + "\n";
    }

    internal static void RequirePrivateLake(string root)
    {
        var lake = Path.Combine(root, ".lake");
        if (new DirectoryInfo(lake).LinkTarget is not null || File.Exists(lake))
            throw new InvalidOperationException(".lake must be a private directory, never a symlink or file");
        if (!Directory.Exists(lake)) return;
        foreach (var path in new[] { "build", "packages", "artifact-cache", "mathlib-cache" })
            if (new DirectoryInfo(Path.Combine(lake, path)).LinkTarget is not null)
                throw new InvalidOperationException(".lake/" + path + " must be private, never a symlink");
    }

    internal static void RequireSuccess(ProcessOutput result, string operation)
    {
        if (result.ExitCode != 0) throw new InvalidOperationException(operation + " failed (exit "
            + result.ExitCode + "): " + Encoding.UTF8.GetString(result.StandardError));
    }
}
