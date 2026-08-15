using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record LeanCacheProvisionResult(
    string Strategy,
    string Method,
    string? Warning);

internal static class LeanCacheProvisioner
{
    internal const int DefaultProvisionBudgetSeconds = 1800;
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    // Cold provisioning spans package clones plus olean download and extraction. Five minutes
    // permits useful fail-fast runs; two hours gives that path 4x headroom without an unbounded hang.
    private static TimeSpan ProvisionBudget
    {
        get
        {
            var raw = Environment.GetEnvironmentVariable("STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS");
            if (int.TryParse(raw, System.Globalization.NumberStyles.Integer, System.Globalization.CultureInfo.InvariantCulture, out var seconds))
            {
                return TimeSpan.FromSeconds(Math.Clamp(seconds, 300, 7200));
            }

            return TimeSpan.FromSeconds(DefaultProvisionBudgetSeconds);
        }
    }

    internal static LeanCacheProvisionResult Provision(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        IWorktreeProcessRunner runner) =>
        Provision(selection, worktreeRoot, runner, new ApfsDirectoryCloner());

    internal static LeanCacheProvisionResult Provision(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner)
    {
        ArgumentNullException.ThrowIfNull(cloner);
        if (selection.Donor is null)
        {
            var notice = $"{selection.Notice}; refusing to clone .lake and running lake exe cache get";
            RunCacheGet(worktreeRoot, runner);
            return new LeanCacheProvisionResult("cache-get", "cache-get", notice);
        }

        var source = Path.Combine(selection.Donor, ".lake");
        var target = Path.Combine(worktreeRoot, ".lake");
        EnsureAbsent(target);

        // One clonefile(2) call clones the entire hierarchy inside the kernel. A per-file walk
        // over the same tree pays a system call per entry and is 55x slower on a warm .lake.
        var clonefileError = cloner.Clone(source, target);
        if (clonefileError is null)
        {
            VerifyPrivateDirectory(target);
            return new LeanCacheProvisionResult("cloned", "clonefile", null);
        }

        RemovePartial(target);
        var copy = runner.Run(
            "cp",
            ["-R", source, target],
            worktreeRoot,
            ProvisionBudget);
        if (copy.ExitCode == 0)
        {
            VerifyPrivateDirectory(target);
            return new LeanCacheProvisionResult(
                "cloned",
                "copy",
                $"clonefile failed ({clonefileError}); used slow ordinary copy");
        }

        var copyError = Error(copy, "cp -R failed");
        RemovePartial(target);
        try
        {
            RunCacheGet(worktreeRoot, runner);
        }
        catch (Exception exception)
        {
            throw new InvalidOperationException(
                $"clonefile failed ({clonefileError}); ordinary copy failed ({copyError}); "
                + $"cache fallback failed ({exception.Message})",
                exception);
        }
        return new LeanCacheProvisionResult(
            "cache-get",
            "cache-get",
            $"clonefile failed ({clonefileError}); ordinary copy failed ({copyError}); used lake exe cache get");
    }

    private static void RunCacheGet(string worktreeRoot, IWorktreeProcessRunner runner)
    {
        var result = runner.Run(
            "lake",
            ["exe", "cache", "get"],
            worktreeRoot,
            ProvisionBudget);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                $"lake exe cache get failed: {Error(result, "unknown error")}");
        }

        VerifyPrivateDirectory(Path.Combine(worktreeRoot, ".lake"));
    }

    private static void EnsureAbsent(string target)
    {
        if (Directory.Exists(target) || File.Exists(target))
        {
            throw new InvalidOperationException($"new worktree unexpectedly contains .lake: {target}");
        }
    }

    private static void VerifyPrivateDirectory(string target)
    {
        if (!Directory.Exists(target))
        {
            throw new InvalidOperationException("cache provisioning completed without creating .lake");
        }

        if (File.GetAttributes(target).HasFlag(FileAttributes.ReparsePoint))
        {
            throw new InvalidOperationException("cache provisioning produced a forbidden .lake symlink");
        }
    }

    private static void RemovePartial(string target)
    {
        if (Directory.Exists(target)) Directory.Delete(target, recursive: true);
        else if (File.Exists(target)) File.Delete(target);
    }

    private static string Error(ProcessOutput output, string fallback)
    {
        var error = StrictUtf8.GetString(output.StandardError).Trim();
        return error.Length == 0 ? fallback : error;
    }
}
