using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record LeanCacheProvisionResult(
    string Strategy,
    string Method,
    string? Warning);

internal static class LeanCacheProvisioner
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static LeanCacheProvisionResult Provision(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        IWorktreeProcessRunner runner)
    {
        if (selection.Donor is null)
        {
            var notice = $"{selection.Notice}; refusing to clone .lake and running lake exe cache get";
            RunCacheGet(worktreeRoot, runner);
            return new LeanCacheProvisionResult("cache-get", "cache-get", notice);
        }

        var source = Path.Combine(selection.Donor, ".lake");
        var target = Path.Combine(worktreeRoot, ".lake");
        EnsureAbsent(target);
        var clonefile = runner.Run(
            "cp",
            ["-c", "-R", source, target],
            worktreeRoot,
            TimeSpan.FromSeconds(1800));
        if (clonefile.ExitCode == 0)
        {
            VerifyPrivateDirectory(target);
            return new LeanCacheProvisionResult("cloned", "clonefile", null);
        }

        var clonefileError = Error(clonefile, "cp -c -R failed");
        RemovePartial(target);
        var copy = runner.Run(
            "cp",
            ["-R", source, target],
            worktreeRoot,
            TimeSpan.FromSeconds(1800));
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
            TimeSpan.FromSeconds(1800));
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
