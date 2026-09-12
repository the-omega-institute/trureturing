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
    internal static TimeSpan DirectoryCopyBudget => LeanCommandBudget;
    internal static TimeSpan DependencyFetchBudget => LeanCommandBudget;

    internal static string Ensure(LeanProcessPolicy policy, LeanPinSet pins, LeanCacheWriterGuard guard)
    {
        var root = policy.Root;
        var lake = Path.Combine(root, ".lake");
        guard.RequireOwnershipOf(lake);
        RequirePrivateLake(root);
        Directory.CreateDirectory(lake);
        var stamp = LeanCacheStamp.Inspect(lake, pins);
        var archive = LeanArchiveAttempt.Skipped("native shared cache available");
        string? warning = null;
        if (stamp.State != LeanCacheStampState.Match)
        {
            // Loading the pinned manifest materializes private package sources without a project build.
            var dependencies = policy.Run(policy.LakeExecutable,
                ["env", OperatingSystem.IsWindows() ? "cmd" : "/usr/bin/true", .. OperatingSystem.IsWindows() ? new[] { "/c", "exit", "0" } : Array.Empty<string>()],
                root, DependencyFetchBudget);
            RequireSuccess(dependencies, "Lake dependency materialization");
            if (!policy.SharedReader && HasMathlib(pins))
            {
                try
                {
                    var fetched = policy.Run(policy.LakeExecutable, ["exe", "cache", "get"], root, DependencyFetchBudget);
                    if (fetched.ExitCode != 0) warning = "private Mathlib cache fetch failed; Lake may rebuild locally: "
                        + Encoding.UTF8.GetString(fetched.StandardError).Trim();
                }
                catch (TimeoutException exception)
                {
                    warning = "private Mathlib cache fetch timed out; Lake may rebuild locally: " + exception.Message;
                }
            }
            if (warning is null) LeanCacheStamp.Write(lake, pins);
        }
        if (!policy.SharedReader)
        {
            var build = Path.Combine(lake, "build");
            var content = LeanCacheStateProbe.InspectContentRoot(build);
            archive = content.Clear && File.Exists(LeanArchiveFetch.ScriptPath(root))
                ? LeanArchiveFetch.Run(root, policy, TimeSpan.FromMinutes(
                    LeanCacheBudgetPolicy.LeanInspectJobBudgetMinutes - LeanCacheBudgetPolicy.PostArchiveReserveMinutes))
                : LeanArchiveAttempt.Skipped(content.Error ?? "private build outputs already present or no release fetcher");
        }
        return "LEAN_CACHE " + JsonSerializer.Serialize(new
        {
            status = warning is null ? "ready" : "degraded", worktree = root,
            mode = policy.SharedReader ? "shared-reader" : "private",
            cache = policy.Cache, reason = warning,
            archive_status = archive.Outcome.ToString().ToLowerInvariant(),
            archive_reason = archive.Reason ?? archive.SkipReason,
        }) + "\n";
    }

    private static bool HasMathlib(LeanPinSet pins)
    {
        using var manifest = JsonDocument.Parse(pins.LakeManifest);
        return manifest.RootElement.TryGetProperty("packages", out var packages)
            && packages.EnumerateArray().Any(package => package.TryGetProperty("name", out var name)
                && name.GetString() == "mathlib");
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
