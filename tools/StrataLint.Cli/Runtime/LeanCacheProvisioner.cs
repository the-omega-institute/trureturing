using System.Text;
using System.Collections.Immutable;
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
    /// <summary>
    /// 无法定位内容层时的回退预算。**这不是那个被派生式取代的 3600**,而是「数不出模块
    /// 就按最保守值走」的兜底:取 clamp 上界,因为「数不出来」多半意味着树不完整,
    /// 此时误杀一个正常构建的代价高于多等一会儿。
    /// </summary>
    internal const int MinProvisionBudgetSeconds = LeanCacheBudgetPolicy.MinimumConfigurableBudgetSeconds;

    /// <summary>
    /// clamp 上界。派生式在仓库约 2225 个内容层模块时算到此值
    /// (2225 × 3 × 1.5 = 10012 > 7200),届时**须重看**:要么该上界随派生式一起长,
    /// 要么承认单次构建不该由本预算兜底而交给 #2814 的 fail-closed 门。
    /// 现读 1651 模块 ⟹ 派生 7429,已略过此界,故当前实际取值即为本上界。
    /// </summary>
    internal const int MaxProvisionBudgetSeconds = LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds;
    private const int MissingOleanSampleLimit = 5;
    internal static ImmutableArray<TimeSpan> CloneRetryBackoffs { get; } =
        [TimeSpan.FromMilliseconds(250), TimeSpan.FromMilliseconds(500),
         TimeSpan.FromMilliseconds(1000), TimeSpan.FromMilliseconds(2000)];
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    // Cold provisioning spans package clones plus olean download and extraction. The five
    // minute floor permits useful fail-fast runs; the two hour ceiling leaves twice the
    // declared default above without an unbounded hang. (That ratio read 4x while the
    // default was 1800s; the policy-override above moved the default and this sentence
    // had to move with it.)
    /// <summary>
    /// 按某棵工作树的内容层规模派生预算。**没有无参版本**:预算依赖那棵树有多少模块,
    /// 一个静态属性只能去猜仓库根,而猜出来的工作量会算出看似派生实则无源的值。
    /// </summary>
    internal static TimeSpan ProvisionBudgetForTree() => ProvisionBudgetFor();

    /// <summary>
    /// 按内容层规模派生本次预算。环境旋钮仍优先,且仍受同一 clamp。
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

    // 以下三个名字**同值**,但继承是显式且带依据的 —— 这正是 #2535 所指「宽域」的收口:
    // 病不在「四个点共用一个数」,而在「共用是隐式的、无人说得出为什么」。
    //
    // 三点的实际发生数(2026-08-23,本会话 47 条 ensure 收据):
    //   cp -R 回退      0 次(clonefile_errno 全为 null)
    //   lake cache get  3 次,离预算差两个数量级(ensure 端到端 13 秒)
    //   任意 Lake 命令  常走,是唯一会接近该值的点
    //
    // 故按第 20″ 条「防的必须是发生过的事」,不为前两者各造一个独立裸数
    // ——那会把一个无源常数变成三个,是「量腹而食」所禁的第四形乘以三。

    /// <summary>
    /// 承重点:`worktree with-cache-writer` 包裹的任意 Lake 命令。**该值就是为它定的**,
    /// 须清过最贵的重建。实测有界工作量:全量内容层冷建 **3388s**(本机 28 核,含并发);
    /// `S0/Tower` 全族 **6305s**(ubuntu-24.04-arm 跨机复测,run 32493250519)。
    /// 分类与退出条件见 <see cref="LeanCacheBudgetPolicy"/> 的 policy-override 声明(案号 #2535)。
    /// </summary>
    internal static TimeSpan LeanCommandBudget => ProvisionBudgetForTree();

    /// <summary>
    /// `cp -R` 目录复制,即 clonefile 失败时的回退路径。**继承 <see cref="LeanCommandBudget"/>,
    /// 不是独立取值**:该路径本机实测 **0 次发生**,为零发生路径派生一个末值会新增一个无源常数,
    /// 违第 20″ 条。若日后收据中出现非 null 的 `clonefile_errno`,该继承即失去依据,
    /// 须按「量腹而食」三型之一为其单独收口并带新案号。
    /// </summary>
    internal static TimeSpan DirectoryCopyBudget => LeanCommandBudget;

    /// <summary>
    /// `lake exe cache get`,依赖层公共供给。**继承 <see cref="LeanCommandBudget"/>,不是独立取值**:
    /// 实测走到 3 次,耗时离该预算差两个数量级(ensure 端到端 13 秒),故它从不是该值的约束方。
    /// 若某次该命令的耗时进入同一量级,该继承即失去依据,须单独收口并带新案号。
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
                DirectoryCopyBudget);
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
