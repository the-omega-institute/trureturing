using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record LeanCacheProvisionResult(
    string Strategy,
    string Method,
    string? Warning,
    MathlibOleanInventory MathlibOleans,
    ClonefileReceipt Clonefile);

internal sealed record MathlibOleanInventory(
    int? MissingFiles,
    IReadOnlyList<string> MissingSamples)
{
    internal static MathlibOleanInventory Unknown { get; } = new(null, []);
}

internal interface ILeanCachePublisher
{
    void Publish(string staged, string target, LeanPinSet pins);
}

internal sealed class LeanCachePublisher : ILeanCachePublisher
{
    internal static LeanCachePublisher Instance { get; } = new();
    private readonly Action<string>? postRenamePreStamp;

    internal LeanCachePublisher(Action<string>? postRenamePreStamp = null)
    {
        this.postRenamePreStamp = postRenamePreStamp;
    }

    public void Publish(string staged, string target, LeanPinSet pins)
    {
        Directory.Move(staged, target);
        postRenamePreStamp?.Invoke(target);
        LeanCacheStamp.Write(target, pins);
    }
}

internal static class LeanCacheProvisioner
{
    private enum CacheTreeOwnership
    {
        CreatedByThisCall,
        PreExisting,
    }

    /// The value and its policy-override declaration live in
    /// <see cref="LeanCacheBudgetPolicy"/>. Keeping the declaration beside the constant
    /// pushed this file past the 800-line limit once dev added to it, and shortening the
    /// declaration to fit would trade an audited statement for a line count.
    internal const int DefaultProvisionBudgetSeconds =
        LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds;
    private const int MissingOleanSampleLimit = 5;
    private static readonly TimeSpan[] CloneRetryBackoffs =
        [TimeSpan.FromMilliseconds(250), TimeSpan.FromMilliseconds(500),
         TimeSpan.FromMilliseconds(1000), TimeSpan.FromMilliseconds(2000)];
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    // Cold provisioning spans package clones plus olean download and extraction. The five
    // minute floor permits useful fail-fast runs; the two hour ceiling leaves twice the
    // declared default above without an unbounded hang. (That ratio read 4x while the
    // default was 1800s; the policy-override above moved the default and this sentence
    // had to move with it.)
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
        string lakeExecutable,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard,
        IDirectoryCloner cloner,
        Action<TimeSpan>? wait = null) =>
        Provision(
            selection,
            worktreeRoot,
            pins,
            lakeExecutable,
            runner,
            writerGuard,
            cloner,
            LeanCachePublisher.Instance,
            RemovePartial,
            wait);

    internal static LeanCacheProvisionResult Provision(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        LeanPinSet pins,
        string lakeExecutable,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard,
        IDirectoryCloner cloner,
        Action<string> removePartial,
        Action<TimeSpan>? wait = null) =>
        Provision(
            selection,
            worktreeRoot,
            pins,
            lakeExecutable,
            runner,
            writerGuard,
            cloner,
            LeanCachePublisher.Instance,
            removePartial,
            wait);

    internal static LeanCacheProvisionResult Provision(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        LeanPinSet pins,
        string lakeExecutable,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard,
        IDirectoryCloner cloner,
        ILeanCachePublisher publisher) =>
        Provision(
            selection,
            worktreeRoot,
            pins,
            lakeExecutable,
            runner,
            writerGuard,
            cloner,
            publisher,
            RemovePartial);

    internal static LeanCacheProvisionResult Provision(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        LeanPinSet pins,
        string lakeExecutable,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard,
        IDirectoryCloner cloner,
        ILeanCachePublisher publisher,
        Action<string> removePartial,
        Action<TimeSpan>? wait = null)
    {
        ArgumentNullException.ThrowIfNull(cloner);
        ArgumentNullException.ThrowIfNull(publisher);
        ArgumentNullException.ThrowIfNull(removePartial);
        wait ??= Thread.Sleep;
        ArgumentNullException.ThrowIfNull(writerGuard);
        writerGuard.RequireOwnershipOf(Path.Combine(worktreeRoot, ".lake"));
        if (selection.Donor is null)
        {
            var notice = Join(
                selection.Notice,
                "refusing to clone .lake and running lake exe cache get");
            return Fetch(
                worktreeRoot,
                pins,
                lakeExecutable,
                runner,
                notice,
                removePartial,
                ClonefileReceipt.NotRun);
        }

        var source = Path.Combine(selection.Donor, ".lake");
        var target = Path.Combine(worktreeRoot, ".lake");
        EnsureAbsent(target);
        var staged = target + ".stage-" + Path.GetRandomFileName();
        string? cloneWarning;
        ClonefileReceipt cloneReceipt;
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
            removePartial,
            wait,
            out cloneReceipt,
            out cloneWarning);
        if (cloned is not null) return cloned;

        return Fetch(
            worktreeRoot,
            pins,
            lakeExecutable,
            runner,
            Join(selection.Notice, cloneWarning),
            removePartial,
            cloneReceipt);
    }

    internal static LeanCacheProvisionResult ReproduceExisting(
        string worktreeRoot,
        LeanPinSet pins,
        string lakeExecutable,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard)
    {
        writerGuard.RequireOwnershipOf(Path.Combine(worktreeRoot, ".lake"));
        var mathlibOleans = RunCacheGet(
            worktreeRoot,
            pins,
            lakeExecutable,
            runner,
            CacheTreeOwnership.PreExisting,
            RemovePartial);
        return new LeanCacheProvisionResult(
            "cache-get",
            "cache-get",
            "ran the current-pin producer in place; the pin-identity stamp was published after the producer completed",
            mathlibOleans,
            ClonefileReceipt.NotRun);
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
        Action<string> removePartial,
        Action<TimeSpan> wait,
        out ClonefileReceipt cloneReceipt,
        out string? warning)
    {
        using var guard = selection.TakeGuard() ?? LeanCacheGuard.TryAcquireShared(source);
        if (guard is null)
        {
            cloneReceipt = ClonefileReceipt.NotRun;
            warning = "donor cache guard is busy";
            return null;
        }

        if (!LeanCacheStamp.Matches(source, pins, out var stampReason)
            || LeanCacheBusyProbe.IsBusy(selection.Donor!, runner))
        {
            cloneReceipt = ClonefileReceipt.NotRun;
            warning = stampReason ?? "donor worktree is busy";
            return null;
        }

        EnsureAbsent(staged);

        // One clonefile(2) call clones the entire hierarchy inside the kernel. A per-file walk
        // over the same tree pays a system call per entry and is roughly 60x slower on a warm .lake.
        var clone = CloneWithRetry(
            source,
            staged,
            cloner,
            removePartial,
            wait,
            out cloneReceipt);

        if (clone.Succeeded)
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
                cloneReceipt,
                removePartial,
                out warning);
        }

        var exit = new CloneReceiptExit(
            cloneReceipt,
            $"clonefile failed ({clone.Message})");
        if (!exit.TryCleanup(staged, removePartial, "staging cleanup"))
        {
            exit.AppendWarning("ordinary copy skipped");
            cloneReceipt = exit.Receipt;
            warning = exit.Warning;
            return null;
        }
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
            exit.AppendWarning($"ordinary copy failed ({exception.Message})");
            exit.TryCleanup(staged, removePartial, "staging cleanup");
            cloneReceipt = exit.Receipt;
            warning = exit.Warning;
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
                Join(exit.Warning, "used slow ordinary copy"),
                exit.Receipt,
                removePartial,
                out warning);
        }

        var copyError = Error(copy, "cp -R failed");
        exit.AppendWarning($"ordinary copy failed ({copyError})");
        exit.TryCleanup(staged, removePartial, "staging cleanup");
        cloneReceipt = exit.Receipt;
        warning = exit.Warning;
        return null;
    }

    private static DirectoryCloneResult CloneWithRetry(
        string source,
        string staged,
        IDirectoryCloner cloner,
        Action<string> removePartial,
        Action<TimeSpan> wait,
        out ClonefileReceipt receipt)
    {
        var attempts = 0;
        var errnos = new List<int>();
        for (var index = 0; ; index++)
        {
            DirectoryCloneResult result;
            try
            {
                result = cloner.Clone(source, staged);
            }
            catch (Exception exception)
            {
                receipt = new ClonefileReceipt(attempts, errnos.ToArray(), null);
                return new DirectoryCloneResult(false, false, null, 0, exception.Message);
            }

            attempts += result.Attempts;
            if (result.Errno is int errno) errnos.Add(errno);
            if (result.Succeeded || !result.Retryable || index == CloneRetryBackoffs.Length)
            {
                receipt = new ClonefileReceipt(attempts, errnos.ToArray(), null);
                return result;
            }

            try
            {
                removePartial(staged);
            }
            catch (Exception exception)
            {
                receipt = new ClonefileReceipt(attempts, errnos.ToArray(), exception.Message);
                return result with
                {
                    Retryable = false,
                    Message = $"{result.Message}; retry cleanup failed ({exception.Message})",
                };
            }
            wait(CloneRetryBackoffs[index]);
        }
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
        ClonefileReceipt cloneReceipt,
        Action<string> removePartial,
        out string? finalWarning)
    {
        var mathlibOleans = MathlibOleanInventory.Unknown;
        try
        {
            VerifyPrivateDirectory(staged);
            RemoveCopiedStamp(staged);
            mathlibOleans = InspectMathlibOleans(staged);
            if (!LeanCacheStamp.Matches(source, pins, out var stampReason)
                || LeanCacheBusyProbe.IsBusy(donorRoot, runner))
            {
                removePartial(staged);
                finalWarning = stampReason ?? "donor became busy after staging; discarded staging copy";
                return null;
            }

            publisher.Publish(staged, target, pins);
        }
        catch (Exception exception)
        {
            var exit = new CloneReceiptExit(cloneReceipt, warning);
            exit.TryCleanup(staged, removePartial, "staging cleanup");
            exit.TryCleanup(target, removePartial, "published cache cleanup");
            throw exit.Wrap(exception);
        }

        finalWarning = warning;
        return new LeanCacheProvisionResult(
            "cloned",
            method,
            warning,
            mathlibOleans,
            cloneReceipt);
    }

    private static LeanCacheProvisionResult Fetch(
        string worktreeRoot,
        LeanPinSet pins,
        string lakeExecutable,
        IWorktreeProcessRunner runner,
        string? warning,
        Action<string> removePartial,
        ClonefileReceipt cloneReceipt)
    {
        try
        {
            var mathlibOleans = RunCacheGet(
                worktreeRoot,
                pins,
                lakeExecutable,
                runner,
                CacheTreeOwnership.CreatedByThisCall,
                removePartial);
            return new LeanCacheProvisionResult(
                "cache-get",
                "cache-get",
                Join(warning, "used lake exe cache get"),
                mathlibOleans,
                cloneReceipt);
        }
        catch (LeanCacheProvisionException exception)
        {
            throw new LeanCacheProvisionException(
                Join(warning, $"cache fallback failed ({exception.Message})"),
                exception,
                cloneReceipt);
        }
        catch (Exception exception)
        {
            throw new LeanCacheProvisionException(
                Join(warning, $"cache fallback failed ({exception.Message})"),
                exception,
                cloneReceipt);
        }
    }

    private static MathlibOleanInventory RunCacheGet(
        string worktreeRoot,
        LeanPinSet pins,
        string lakeExecutable,
        IWorktreeProcessRunner runner,
        CacheTreeOwnership ownership,
        Action<string> removePartial)
    {
        var lake = Path.Combine(worktreeRoot, ".lake");
        try
        {
            var result = runner.Run(
                lakeExecutable,
                ["exe", "cache", "get"],
                worktreeRoot,
                ProvisionBudget);
            if (result.ExitCode != 0)
            {
                throw new LeanCacheProvisionException(
                    $"lake exe cache get failed: {Error(result, "unknown error")}");
            }

            VerifyPrivateDirectory(lake);
            var mathlibOleans = InspectMathlibOleans(lake);

            try
            {
                LeanCacheStamp.Write(lake, pins);
            }
            catch (Exception exception)
            {
                throw new LeanCacheProvisionException(
                    $"cache producer stamp publication failed: {exception.Message}",
                    exception);
            }
            return mathlibOleans;
        }
        catch (Exception exception)
        {
            if (ownership == CacheTreeOwnership.CreatedByThisCall)
            {
                try
                {
                    removePartial(lake);
                }
                catch (Exception cleanupException)
                {
                    var aggregate = new AggregateException(exception, cleanupException);
                    if (exception is LeanCacheProvisionException provisionException)
                    {
                        throw new LeanCacheProvisionException(
                            provisionException.Message,
                            aggregate);
                    }
                    throw new LeanCacheProvisionException(
                        exception.Message,
                        aggregate);
                }
            }
            if (exception is LeanCacheProvisionException) throw;
            throw new LeanCacheProvisionException(
                exception.Message,
                exception);
        }
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

    internal static MathlibOleanInventory InspectMathlibOleans(string lake)
    {
        try
        {
            var mathlib = Path.Combine(lake, "packages", "mathlib");
            var sourceRoot = Path.Combine(mathlib, "Mathlib");
            if (!Directory.Exists(sourceRoot)) return MathlibOleanInventory.Unknown;

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

            return sourceCount == 0
                ? MathlibOleanInventory.Unknown
                : new MathlibOleanInventory(missingCount, samples);
        }
        catch
        {
            return MathlibOleanInventory.Unknown;
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
