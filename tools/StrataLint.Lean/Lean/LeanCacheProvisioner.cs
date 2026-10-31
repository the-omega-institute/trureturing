using StrataLint.Runtime;
using System.Text;
using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

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
        // Release extraction and rollback directories are not reusable cache. Strip them
        // only from this private clone; directory links are deleted without following them.
        const string releasePrefix = ".release-";
        foreach (var directory in Directory.EnumerateDirectories(staged))
        {
            var name = Path.GetFileName(directory);
            if (name.StartsWith(releasePrefix, StringComparison.Ordinal)
                && name.Length > releasePrefix.Length
                && name[releasePrefix.Length..].All(static character =>
                    char.IsAsciiLetterOrDigit(character) || character is '_' or '-'))
                Directory.Delete(directory, recursive: true);
        }
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

    /// <summary>
    /// Configured per-command cutoff floor (300s); absent or invalid configuration uses
    /// the ceiling. Value, provenance and selected scope live in <see cref="LeanCacheBudgetPolicy"/>.
    /// </summary>
    internal const int MinProvisionBudgetSeconds = LeanCacheBudgetPolicy.MinimumConfigurableBudgetSeconds;

    /// <summary>
    /// Fixed default and clamp ceiling; a bounded admitted attempt, not a cold-completion promise.
    /// </summary>
    internal const int MaxProvisionBudgetSeconds = LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds;
    private const int MissingOleanSampleLimit = 5;
    internal static ImmutableArray<TimeSpan> CloneRetryBackoffs { get; } =
        [TimeSpan.FromMilliseconds(250), TimeSpan.FromMilliseconds(500),
         TimeSpan.FromMilliseconds(1000), TimeSpan.FromMilliseconds(2000)];
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    /// <summary>
    /// Compatibility accessor for the configured finite command cutoff. No tree census
    /// or cache-closure validation participates in this value.
    /// </summary>
    internal static TimeSpan ProvisionBudgetForTree() => ProvisionBudgetFor();

    /// <summary>
    /// 解析环境旋钮并 clamp;无旋钮即上界。无派生、无树读取。
    /// </summary>
    internal static TimeSpan ProvisionBudgetFor()
    {
        var raw = Environment.GetEnvironmentVariable("STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS");
        if (int.TryParse(raw, System.Globalization.NumberStyles.Integer, System.Globalization.CultureInfo.InvariantCulture, out var seconds))
        {
            return TimeSpan.FromSeconds(
                Math.Clamp(seconds, MinProvisionBudgetSeconds, MaxProvisionBudgetSeconds));
        }

        return TimeSpan.FromSeconds(MaxProvisionBudgetSeconds);
    }

    /// <summary>
    /// Cutoff forwarded to each command admitted by with-cache-reader / with-cache-writer.
    /// Known Project Cold needs exact consent, either probe failure refuses, and known
    /// Project Warm remains incremental without consent. Warmth is only an any-olean probe;
    /// neither admission nor this cutoff certifies current closure or successful completion.
    /// Policy scope, historical readings and review conditions are in <see cref="LeanCacheBudgetPolicy"/>.
    /// </summary>
    internal static TimeSpan LeanCommandBudget => ProvisionBudgetForTree();

    /// <summary>
    /// Cache get explicitly inherits the command cutoff rather than a separate capacity promise.
    /// Historical #2535 readings observed three fetches and a 13s end-to-end ensure, not a
    /// current dependency-fetch benchmark. Review inheritance if actual fetches approach the cap.
    /// </summary>
    internal static TimeSpan DependencyFetchBudget => LeanCommandBudget;

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
        wait ??= WaitForRetry;
        ArgumentNullException.ThrowIfNull(writerGuard);
        var target = Path.Combine(worktreeRoot, ".lake");
        writerGuard.RequireOwnershipOf(target);

        // Provision 是**新建树**的 API:目标必须在此刻不存在。这一条此前只写在 donor
        // 分支里(clone 之前),于是「无 donor」那条路进来时目标是否存在无人过问。
        //
        // 把它上移到公共支配点,是为了让下游那句「这棵 .lake 是本次调用造的」成为
        // **机器强制的契约**,而不是靠读控制流推出来的结论。推出来的结论会随重构失效:
        // ensure 在 stamp Mismatch 时会先删掉整个 .lake 再落到这里(`RemoveProjection`),
        // 所以「到达这里 ⟹ 调用入口时 .lake 不存在」**是假的**;真正成立的是
        // 「到达这里 ⟹ **在这个边界上** .lake 不存在」—— 而那要由这一行来保证。
        //
        // 现有树的路径是 `ReproduceExisting`(它传 `CacheTreeOwnership.PreExisting`),
        // 不经过这里。两条路各有各的 API,不共用。
        EnsureAbsent(target);
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
        var staged = target + ".stage-" + Path.GetRandomFileName();
        string? cloneWarning;
        ClonefileReceipt cloneReceipt;
        var cloned = TryClone(
            selection,
            source,
            staged,
            target,
            pins,
            runner,
            cloner,
            publisher,
            removePartial,
            wait,
            out cloneReceipt,
            out cloneWarning);
        if (cloned is not null) return cloned;

        throw new LeanCacheProvisionException(
            Join(Join(selection.Notice, cloneWarning), "donor clonefile seeding failed"),
            clonefile: cloneReceipt);
    }

    internal static LeanCacheProvisionResult ProvisionFromRequiredDonor(
        LeanCacheDonorSelection selection,
        string worktreeRoot,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard writerGuard,
        IDirectoryCloner cloner,
        Action<string> removePartial,
        Action<TimeSpan>? wait = null)
    {
        ArgumentNullException.ThrowIfNull(selection);
        ArgumentNullException.ThrowIfNull(cloner);
        ArgumentNullException.ThrowIfNull(removePartial);
        ArgumentNullException.ThrowIfNull(writerGuard);
        if (selection.Donor is null)
            throw new InvalidOperationException("required cache donor is unavailable");

        wait ??= WaitForRetry;
        var target = Path.Combine(worktreeRoot, ".lake");
        writerGuard.RequireOwnershipOf(target);
        EnsureAbsent(target);
        var source = Path.Combine(selection.Donor, ".lake");
        var staged = target + ".stage-" + Path.GetRandomFileName();
        var cloned = TryClone(
            selection,
            source,
            staged,
            target,
            pins,
            runner,
            cloner,
            LeanCachePublisher.Instance,
            removePartial,
            wait,
            out var cloneReceipt,
            out var cloneWarning);
        if (cloned is not null) return cloned;

        throw new LeanCacheProvisionException(
            Join(cloneWarning, "required main-checkout donor clonefile seeding failed"),
            clonefile: cloneReceipt);
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
        exit.TryCleanup(staged, removePartial, "staging cleanup");
        cloneReceipt = exit.Receipt;
        warning = exit.Warning;
        return null;
    }

    internal static DirectoryCloneResult CloneWithRetry(
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
                cloneReceipt,
                exception.SafeToContinueToBuild);
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
            ProcessOutput result;
            try
            {
                result = runner.Run(
                    lakeExecutable,
                    ["exe", "cache", "get"],
                    worktreeRoot,
                    DependencyFetchBudget);
            }
            catch (Exception exception)
            {
                throw new LeanCacheProvisionException(
                    $"lake exe cache get failed: {exception.Message}",
                    exception,
                    safeToContinueToBuild: true);
            }
            if (result.ExitCode != 0)
            {
                throw new LeanCacheProvisionException(
                    $"lake exe cache get failed: {Error(result, "unknown error")}",
                    safeToContinueToBuild: true);
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
                    exception, safeToContinueToBuild: ownership == CacheTreeOwnership.PreExisting);
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

    internal static void VerifyPrivateDirectory(string target)
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

    internal static void RemovePartial(string target)
    {
        if (Directory.Exists(target)) Directory.Delete(target, recursive: true);
        else if (File.Exists(target)) File.Delete(target);
    }

    internal static void WaitForRetry(TimeSpan delay)
    {
        using var retrySignal = new ManualResetEventSlim(initialState: false);
        retrySignal.Wait(delay);
    }

    internal static string Error(ProcessOutput output, string fallback)
    {
        var error = StrictUtf8.GetString(output.StandardError).Trim();
        return error.Length == 0 ? fallback : error;
    }

    internal static string Join(string? first, string? second)
    {
        if (string.IsNullOrWhiteSpace(first)) return second ?? string.Empty;
        if (string.IsNullOrWhiteSpace(second)) return first;
        return first + "; " + second;
    }
}
