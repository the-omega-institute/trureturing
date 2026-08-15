using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record LeanCacheProvisionResult(
    string Strategy,
    string Method,
    string? Warning,
    int? MathlibCachePrunedFiles);

internal sealed class MathlibOleanCompletenessException : InvalidOperationException
{
    internal MathlibOleanCompletenessException(
        int? missingOleanFiles,
        IReadOnlyList<string> missingOleanSamples,
        string message,
        Exception? innerException = null)
        : base(message, innerException)
    {
        MissingOleanFiles = missingOleanFiles;
        MissingOleanSamples = missingOleanSamples;
    }

    internal int? MissingOleanFiles { get; }

    internal IReadOnlyList<string> MissingOleanSamples { get; }
}

internal static class LeanCacheProvisioner
{
    internal const int DefaultProvisionBudgetSeconds = 1800;
    private const int MissingOleanSampleLimit = 5;
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

    internal static TimeSpan CommandBudget => ProvisionBudget;

    internal static LeanCacheProvisionResult Provision(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner)
    {
        if (selection.Donor is null)
        {
            var notice = Join(
                selection.Notice,
                "refusing to clone .lake and running lake exe cache get");
            return Fetch(worktreeRoot, pins, runner, notice);
        }

        var source = Path.Combine(selection.Donor, ".lake");
        var target = Path.Combine(worktreeRoot, ".lake");
        EnsureAbsent(target);
        var staged = target + ".stage-" + Path.GetRandomFileName();
        string? cloneWarning;
        var cloned = TryClone(
            selection,
            source,
            staged,
            target,
            worktreeRoot,
            pins,
            runner,
            out cloneWarning);
        if (cloned is not null) return cloned;

        return Fetch(
            worktreeRoot,
            pins,
            runner,
            Join(selection.Notice, cloneWarning));
    }

    private static LeanCacheProvisionResult? TryClone(
        LeanCacheDonorSelection selection,
        string source,
        string staged,
        string target,
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        out string? warning)
    {
        using var guard = selection.TakeGuard() ?? LeanCacheGuard.TryAcquireShared(source);
        if (guard is null)
        {
            warning = "donor cache guard is busy";
            return null;
        }

        if (!LeanCacheStamp.Matches(source, pins, out var stampReason)
            || LeanCacheBusyProbe.IsBusy(selection.Donor!, runner))
        {
            warning = stampReason ?? "donor worktree is busy";
            return null;
        }

        try
        {
            EnsureAbsent(staged);
            var clonefile = runner.Run(
                "cp",
                ["-c", "-R", source, staged],
                worktreeRoot,
                ProvisionBudget);
            if (clonefile.ExitCode == 0)
            {
                return PublishStaged(
                    source,
                    staged,
                    target,
                    selection.Donor!,
                    pins,
                    runner,
                    "clonefile",
                    null,
                    out warning);
            }

            var clonefileError = Error(clonefile, "cp -c -R failed");
            RemovePartial(staged);
            var copy = runner.Run(
                "cp",
                ["-R", source, staged],
                worktreeRoot,
                ProvisionBudget);
            if (copy.ExitCode == 0)
            {
                return PublishStaged(
                    source,
                    staged,
                    target,
                    selection.Donor!,
                    pins,
                    runner,
                    "copy",
                    $"clonefile failed ({clonefileError}); used slow ordinary copy",
                    out warning);
            }

            var copyError = Error(copy, "cp -R failed");
            warning = $"clonefile failed ({clonefileError}); ordinary copy failed ({copyError})";
            RemovePartial(staged);
            return null;
        }
        catch (Exception exception)
        {
            RemovePartial(staged);
            warning = $"donor staging failed ({exception.Message})";
            return null;
        }
    }

    private static LeanCacheProvisionResult? PublishStaged(
        string source,
        string staged,
        string target,
        string donorRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        string method,
        string? warning,
        out string? finalWarning)
    {
        VerifyPrivateDirectory(staged);
        if (!LeanCacheStamp.Matches(source, pins, out var stampReason)
            || LeanCacheBusyProbe.IsBusy(donorRoot, runner))
        {
            RemovePartial(staged);
            finalWarning = stampReason ?? "donor became busy after staging; discarded staging copy";
            return null;
        }

        VerifyMathlibOleans(staged);
        LeanCacheStamp.Write(staged, pins);
        Directory.Move(staged, target);
        finalWarning = warning;
        return new LeanCacheProvisionResult("cloned", method, warning, null);
    }

    private static LeanCacheProvisionResult Fetch(
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        string? warning)
    {
        try
        {
            var pruned = RunCacheGet(worktreeRoot, pins, runner);
            return new LeanCacheProvisionResult(
                "cache-get",
                "cache-get",
                Join(warning, "used lake exe cache get then lake exe cache clean"),
                pruned);
        }
        catch (MathlibOleanCompletenessException exception)
        {
            throw new MathlibOleanCompletenessException(
                exception.MissingOleanFiles,
                exception.MissingOleanSamples,
                Join(warning, $"cache fallback failed ({exception.Message})"),
                exception);
        }
        catch (Exception exception)
        {
            throw new InvalidOperationException(
                Join(warning, $"cache fallback failed ({exception.Message})"),
                exception);
        }
    }

    private static int RunCacheGet(
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner)
    {
        var lake = Path.Combine(worktreeRoot, ".lake");
        try
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

            VerifyPrivateDirectory(lake);
            VerifyMathlibOleans(lake);
            var sharedCache = MathlibCacheDirectory(worktreeRoot);
            var beforeClean = CountLtarFiles(sharedCache);
            var clean = runner.Run(
                "lake",
                ["exe", "cache", "clean"],
                worktreeRoot,
                ProvisionBudget);
            if (clean.ExitCode != 0)
            {
                throw new InvalidOperationException(
                    $"lake exe cache clean failed: {Error(clean, "unknown error")}");
            }

            var afterClean = CountLtarFiles(sharedCache);
            LeanCacheStamp.Write(lake, pins);
            return Math.Max(0, beforeClean - afterClean);
        }
        catch
        {
            RemovePartial(lake);
            throw;
        }
    }

    private static string MathlibCacheDirectory(string worktreeRoot)
    {
        var explicitPath = Environment.GetEnvironmentVariable("MATHLIB_CACHE_DIR");
        if (!string.IsNullOrEmpty(explicitPath)) return Path.GetFullPath(explicitPath);
        var xdg = Environment.GetEnvironmentVariable("XDG_CACHE_HOME");
        if (!string.IsNullOrEmpty(xdg)) return Path.GetFullPath(Path.Combine(xdg, "mathlib"));
        var home = Environment.GetEnvironmentVariable("HOME");
        return string.IsNullOrEmpty(home)
            ? Path.Combine(worktreeRoot, ".cache")
            : Path.Combine(home, ".cache", "mathlib");
    }

    private static int CountLtarFiles(string directory) => Directory.Exists(directory)
        ? Directory.EnumerateFiles(directory, "*.ltar", SearchOption.AllDirectories).Count()
        : 0;

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

    private static void VerifyMathlibOleans(string lake)
    {
        var mathlib = Path.Combine(lake, "packages", "mathlib");
        var sourceRoot = Path.Combine(mathlib, "Mathlib");
        if (!Directory.Exists(sourceRoot))
        {
            throw new MathlibOleanCompletenessException(
                null,
                [],
                "mathlib olean completeness could not be determined: Mathlib source directory is missing");
        }

        var buildRoot = Path.Combine(mathlib, ".lake", "build", "lib", "lean");
        var sourceCount = 0;
        var missingCount = 0;
        var samples = new List<string>();
        foreach (var source in Directory.EnumerateFiles(
            sourceRoot,
            "*.lean",
            SearchOption.AllDirectories))
        {
            sourceCount++;
            var relative = Path.GetRelativePath(mathlib, source);
            var expected = Path.Combine(buildRoot, Path.ChangeExtension(relative, ".olean"));
            if (File.Exists(expected)) continue;

            missingCount++;
            if (samples.Count < MissingOleanSampleLimit)
            {
                samples.Add(
                    Path.ChangeExtension(relative, null)!
                        .Replace(Path.DirectorySeparatorChar, '/'));
            }
        }

        if (sourceCount == 0)
        {
            throw new MathlibOleanCompletenessException(
                null,
                [],
                "mathlib olean completeness could not be determined: Mathlib source directory contains no Lean files");
        }

        if (missingCount != 0)
        {
            throw new MathlibOleanCompletenessException(
                missingCount,
                samples,
                $"mathlib olean cache is incomplete: missing {missingCount} of {sourceCount}; "
                + $"samples: {string.Join(", ", samples)}");
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

    private static string Join(string? first, string? second)
    {
        if (string.IsNullOrWhiteSpace(first)) return second ?? string.Empty;
        if (string.IsNullOrWhiteSpace(second)) return first;
        return first + "; " + second;
    }
}
