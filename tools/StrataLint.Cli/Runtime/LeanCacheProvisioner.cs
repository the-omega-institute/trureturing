using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record LeanCacheProvisionResult(
    string Strategy,
    string Method,
    string? Warning,
    MathlibCachePruneOutcome PruneOutcome);

internal sealed record MathlibCachePruneOutcome(
    string Scope,
    int? DeletedFiles,
    string CleanStatus)
{
    internal static MathlibCachePruneOutcome NotRun { get; } = new("machine", 0, "not-run");
}

internal interface ILeanCachePublisher
{
    void Publish(string staged, string target, LeanPinSet pins);
}

internal sealed class LeanCachePublisher : ILeanCachePublisher
{
    internal static LeanCachePublisher Instance { get; } = new();

    private LeanCachePublisher()
    {
    }

    public void Publish(string staged, string target, LeanPinSet pins)
    {
        Directory.Move(staged, target);
        LeanCacheStamp.Write(target, pins);
    }
}

internal class LeanCacheProvisionException : InvalidOperationException
{
    internal LeanCacheProvisionException(
        string message,
        MathlibCachePruneOutcome pruneOutcome,
        Exception? innerException = null)
        : base(message, innerException) => PruneOutcome = pruneOutcome;

    internal MathlibCachePruneOutcome PruneOutcome { get; }
}

internal sealed class MathlibOleanCompletenessException : LeanCacheProvisionException
{
    internal MathlibOleanCompletenessException(
        int? missingOleanFiles,
        IReadOnlyList<string> missingOleanSamples,
        string message,
        MathlibCachePruneOutcome? pruneOutcome = null,
        Exception? innerException = null)
        : base(message, pruneOutcome ?? MathlibCachePruneOutcome.NotRun, innerException)
    {
        MissingOleanFiles = missingOleanFiles;
        MissingOleanSamples = missingOleanSamples;
    }

    internal int? MissingOleanFiles { get; }

    internal IReadOnlyList<string> MissingOleanSamples { get; }
}

internal static class LeanCacheProvisioner
{
    private enum CacheTreeOwnership
    {
        CreatedByThisCall,
        PreExisting,
    }

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
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard) =>
        Provision(selection, worktreeRoot, pins, runner, writerGuard, new ApfsDirectoryCloner());

    internal static LeanCacheProvisionResult Provision(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard,
        IDirectoryCloner cloner) =>
        Provision(
            selection,
            worktreeRoot,
            pins,
            runner,
            writerGuard,
            cloner,
            LeanCachePublisher.Instance);

    internal static LeanCacheProvisionResult Provision(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard,
        IDirectoryCloner cloner,
        ILeanCachePublisher publisher)
    {
        ArgumentNullException.ThrowIfNull(cloner);
        ArgumentNullException.ThrowIfNull(publisher);
        ArgumentNullException.ThrowIfNull(writerGuard);
        writerGuard.RequireOwnershipOf(Path.Combine(worktreeRoot, ".lake"));
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
            cloner,
            publisher,
            out cloneWarning);
        if (cloned is not null) return cloned;

        return Fetch(
            worktreeRoot,
            pins,
            runner,
            Join(selection.Notice, cloneWarning));
    }

    internal static LeanCacheProvisionResult ReproduceExisting(
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard) =>
        ReproduceExisting(worktreeRoot, pins, runner, writerGuard, CountLtarFiles);

    internal static LeanCacheProvisionResult ReproduceExisting(
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard,
        Func<string, int> countLtarFiles)
    {
        ArgumentNullException.ThrowIfNull(countLtarFiles);
        writerGuard.RequireOwnershipOf(Path.Combine(worktreeRoot, ".lake"));
        var pruneOutcome = RunCacheGet(
            worktreeRoot,
            pins,
            runner,
            CacheTreeOwnership.PreExisting,
            countLtarFiles);
        return new LeanCacheProvisionResult(
            "cache-get",
            "cache-get",
            "ran the current-pin producer in place; the pin-identity stamp was published only after producer and live completeness verification succeeded",
            pruneOutcome);
    }

    private static LeanCacheProvisionResult? TryClone(
        LeanCacheDonorSelection selection,
        string source,
        string staged,
        string target,
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        ILeanCachePublisher publisher,
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

        EnsureAbsent(staged);

        // One clonefile(2) call clones the entire hierarchy inside the kernel. A per-file walk
        // over the same tree pays a system call per entry and is roughly 60x slower on a warm .lake.
        string? clonefileError;
        try
        {
            clonefileError = cloner.Clone(source, staged);
        }
        catch (Exception exception)
        {
            RemovePartial(staged);
            clonefileError = exception.Message;
        }

        if (clonefileError is null)
        {
            return PublishStaged(
                source,
                staged,
                target,
                selection.Donor!,
                pins,
                runner,
                publisher,
                "clonefile",
                null,
                out warning);
        }

        RemovePartial(staged);
        ProcessOutput copy;
        try
        {
            copy = runner.Run(
                "cp",
                ["-R", source, staged],
                worktreeRoot,
                ProvisionBudget);
        }
        catch (Exception exception)
        {
            RemovePartial(staged);
            warning = $"clonefile failed ({clonefileError}); ordinary copy failed ({exception.Message})";
            return null;
        }

        if (copy.ExitCode == 0)
        {
            return PublishStaged(
                source,
                staged,
                target,
                selection.Donor!,
                pins,
                runner,
                publisher,
                "copy",
                $"clonefile failed ({clonefileError}); used slow ordinary copy",
                out warning);
        }

        var copyError = Error(copy, "cp -R failed");
        warning = $"clonefile failed ({clonefileError}); ordinary copy failed ({copyError})";
        RemovePartial(staged);
        return null;
    }

    private static LeanCacheProvisionResult? PublishStaged(
        string source,
        string staged,
        string target,
        string donorRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        ILeanCachePublisher publisher,
        string method,
        string? warning,
        out string? finalWarning)
    {
        try
        {
            VerifyPrivateDirectory(staged);
            RemoveCopiedStamp(staged);
            VerifyMathlibOleans(staged);
            if (!LeanCacheStamp.Matches(source, pins, out var stampReason)
                || LeanCacheBusyProbe.IsBusy(donorRoot, runner))
            {
                RemovePartial(staged);
                finalWarning = stampReason ?? "donor became busy after staging; discarded staging copy";
                return null;
            }

            publisher.Publish(staged, target, pins);
        }
        catch
        {
            RemovePartial(staged);
            RemovePartial(target);
            throw;
        }

        finalWarning = warning;
        return new LeanCacheProvisionResult(
            "cloned",
            method,
            warning,
            MathlibCachePruneOutcome.NotRun);
    }

    private static LeanCacheProvisionResult Fetch(
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        string? warning)
    {
        try
        {
            var pruneOutcome = RunCacheGet(
                worktreeRoot,
                pins,
                runner,
                CacheTreeOwnership.CreatedByThisCall,
                CountLtarFiles);
            return new LeanCacheProvisionResult(
                "cache-get",
                "cache-get",
                Join(warning, "used lake exe cache get then lake exe cache clean"),
                pruneOutcome);
        }
        catch (MathlibOleanCompletenessException exception)
        {
            throw new MathlibOleanCompletenessException(
                exception.MissingOleanFiles,
                exception.MissingOleanSamples,
                Join(warning, $"cache fallback failed ({exception.Message})"),
                exception.PruneOutcome,
                exception);
        }
        catch (LeanCacheProvisionException exception)
        {
            throw new LeanCacheProvisionException(
                Join(warning, $"cache fallback failed ({exception.Message})"),
                exception.PruneOutcome,
                exception);
        }
        catch (Exception exception)
        {
            throw new LeanCacheProvisionException(
                Join(warning, $"cache fallback failed ({exception.Message})"),
                MathlibCachePruneOutcome.NotRun,
                exception);
        }
    }

    private static MathlibCachePruneOutcome RunCacheGet(
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        CacheTreeOwnership ownership,
        Func<string, int> countLtarFiles)
    {
        var lake = Path.Combine(worktreeRoot, ".lake");
        var pruneOutcome = MathlibCachePruneOutcome.NotRun;
        try
        {
            var result = runner.Run(
                "lake",
                ["exe", "cache", "get"],
                worktreeRoot,
                ProvisionBudget);
            if (result.ExitCode != 0)
            {
                throw new LeanCacheProvisionException(
                    $"lake exe cache get failed: {Error(result, "unknown error")}",
                    pruneOutcome);
            }

            VerifyPrivateDirectory(lake);
            VerifyMathlibOleans(lake);
            var sharedCache = MathlibCacheDirectory(worktreeRoot);
            var beforeClean = countLtarFiles(sharedCache);
            pruneOutcome = new MathlibCachePruneOutcome("machine", null, "attempted");
            ProcessOutput clean;
            try
            {
                clean = runner.Run(
                    "lake",
                    ["exe", "cache", "clean"],
                    worktreeRoot,
                    ProvisionBudget);
            }
            catch (Exception exception)
            {
                pruneOutcome = new MathlibCachePruneOutcome("machine", null, "failed");
                try
                {
                    var afterFailedClean = countLtarFiles(sharedCache);
                    pruneOutcome = pruneOutcome with
                    {
                        DeletedFiles = Math.Max(0, beforeClean - afterFailedClean),
                    };
                }
                catch (Exception inventoryException)
                {
                    throw new LeanCacheProvisionException(
                        $"lake exe cache clean failed: {exception.Message}; "
                        + $"post-clean cache inventory failed: {inventoryException.Message}",
                        pruneOutcome,
                        new AggregateException(exception, inventoryException));
                }
                throw new LeanCacheProvisionException(
                    $"lake exe cache clean failed: {exception.Message}",
                    pruneOutcome,
                    exception);
            }
            pruneOutcome = new MathlibCachePruneOutcome(
                "machine",
                null,
                clean.ExitCode == 0 ? "succeeded" : "failed");
            try
            {
                var afterClean = countLtarFiles(sharedCache);
                pruneOutcome = pruneOutcome with
                {
                    DeletedFiles = Math.Max(0, beforeClean - afterClean),
                };
            }
            catch (Exception inventoryException)
            {
                throw new LeanCacheProvisionException(
                    $"lake exe cache clean {pruneOutcome.CleanStatus}; "
                    + $"post-clean cache inventory failed: {inventoryException.Message}",
                    pruneOutcome,
                    inventoryException);
            }
            if (clean.ExitCode != 0)
            {
                throw new LeanCacheProvisionException(
                    $"lake exe cache clean failed: {Error(clean, "unknown error")}",
                    pruneOutcome);
            }

            try
            {
                LeanCacheStamp.Write(lake, pins);
            }
            catch (Exception exception)
            {
                throw new LeanCacheProvisionException(
                    $"cache producer stamp publication failed: {exception.Message}",
                    pruneOutcome,
                    exception);
            }
            return pruneOutcome;
        }
        catch (Exception exception)
        {
            if (ownership == CacheTreeOwnership.CreatedByThisCall) RemovePartial(lake);
            if (exception is LeanCacheProvisionException) throw;
            throw new LeanCacheProvisionException(
                exception.Message,
                pruneOutcome,
                exception);
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

    internal static void VerifyMathlibOleans(string lake)
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

    private static void RemoveCopiedStamp(string staged)
    {
        var stamp = LeanCacheStamp.PathFor(staged);
        if (File.Exists(stamp))
        {
            File.Delete(stamp);
            return;
        }
        if (Directory.Exists(stamp))
        {
            throw new InvalidOperationException(
                "staging cache contains a producer stamp that is not a regular file");
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
