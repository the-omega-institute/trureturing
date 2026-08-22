using System.Text;
using System.Text.Json;

namespace StrataLint.Cli;

internal static class LeanCacheEnsureCommand
{
    internal const string Usage = "USAGE: StrataLint worktree ensure-cache [--path DIR]";
    internal const string WriterUsage =
        "USAGE: StrataLint worktree with-cache-writer [--path DIR] -- COMMAND [ARG ...]";

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner) =>
        Run(
            repositoryRoot,
            arguments,
            runner,
            cloner,
            LeanCacheProvisioner.CountLtarFiles,
            removePartial: null);

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        Func<string, int> countLtarFiles,
        Action<string>? removePartial = null)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);
        ArgumentNullException.ThrowIfNull(cloner);
        ArgumentNullException.ThrowIfNull(countLtarFiles);
        if (!TryParseWorktreeRoot(repositoryRoot, arguments, out var root))
        {
            return new CommandResult(false, string.Empty, Usage + "\n");
        }

        var pins = LeanPinSet.TryReadWorktree(root, out var pinReason);
        if (pins is null)
        {
            return FailureReceipt(
                "failed",
                root,
                donor: null,
                method: "none",
                pinSha256: null,
                reason: pinReason ?? "Lean pin files are unavailable");
        }

        if (!LeanLakeExecutable.TryResolve(out var lakeExecutable, out var lakeReason))
        {
            return FailureReceipt(
                "failed",
                root,
                donor: null,
                method: "none",
                pins.Sha256,
                lakeReason);
        }

        var lake = Path.Combine(root, ".lake");
        using var guard = LeanCacheWriterGuard.TryAcquire(lake);
        if (guard is null)
        {
            return FailureReceipt(
                "busy",
                root,
                donor: null,
                method: "none",
                pins.Sha256,
                "canonical cache writer guard is busy");
        }

        // 显式预热这条路径同样从 donor clone，故同样先刷新货源。
        // 只覆盖 `make lean` 那条会让 `make lean-cache-ensure` 照旧取到陈旧缓存——
        // 这一条是被测试的红逼出来的:判据原本只看文件里第一个 clone 点。
        _ = LeanDonorRefresh.TryRefresh(repositoryRoot, root, runner);

        return EnsureLocked(
            root,
            pins,
            lakeExecutable,
            runner,
            cloner,
            guard,
            countLtarFiles,
            removePartial);
    }

    internal static CommandResult RunWithWriter(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner)
    {
        ArgumentNullException.ThrowIfNull(cloner);
        if (!TryParseWriter(repositoryRoot, arguments, out var root, out var command))
        {
            return new CommandResult(false, string.Empty, WriterUsage + "\n");
        }

        var pins = LeanPinSet.TryReadWorktree(root, out var pinReason);
        if (pins is null)
        {
            return FailureReceipt(
                "failed",
                root,
                donor: null,
                method: "none",
                pinSha256: null,
                reason: pinReason ?? "Lean pin files are unavailable");
        }

        using var guard = LeanCacheWriterGuard.TryAcquire(Path.Combine(root, ".lake"));
        if (guard is null)
        {
            return FailureReceipt(
                "busy",
                root,
                donor: null,
                method: "none",
                pins.Sha256,
                "canonical cache writer guard is busy");
        }

        // 先把货源刷到当前 dev，再从它 clone。`SelectDonor` 优先选主检出，
        // 但从不保证它是新的——实测停在七天前，于是 ensure 成功却仍要补七天差量。
        // 刷新走既有锁协议的排他端，与随后的共享端 clone 严格串行:
        // 刷新期间的 `lake build` 会让 `LeanCacheBusyProbe` 判 donor 忙，交错即互相拒绝。
        // 尽力而为:失败或抢不到锁都只是少一次加速，绝不挡住本次构建。
        var refreshed = LeanDonorRefresh.TryRefresh(repositoryRoot, root, runner);

        var ensured = EnsureLocked(
            root,
            pins,
            command[0],
            runner,
            cloner,
            guard,
            LeanCacheProvisioner.CountLtarFiles,
            removePartial: null);
        if (!ensured.Success) return ensured;

        try
        {
            var invoked = runner.Run(
                command[0],
                command.Skip(1).ToArray(),
                root,
                LeanCacheProvisioner.CommandBudget);
            return new CommandResult(
                invoked.ExitCode == 0,
                ensured.Output + Encoding.UTF8.GetString(invoked.StandardOutput),
                Encoding.UTF8.GetString(invoked.StandardError));
        }
        catch (Exception exception)
        {
            return new CommandResult(false, ensured.Output, exception.Message + "\n");
        }
    }

    private static CommandResult EnsureLocked(
        string root,
        LeanPinSet pins,
        string lakeExecutable,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        LeanCacheWriterGuard writerGuard,
        Func<string, int> countLtarFiles,
        Action<string>? removePartial)
    {
        var lake = Path.Combine(root, ".lake");
        writerGuard.RequireOwnershipOf(lake);
        string? stampMiss = null;
        try
        {
            if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);

            string? missReason = null;
            if (Directory.Exists(lake))
            {
                var stamp = LeanCacheStamp.Inspect(lake, pins);
                missReason = stamp.Reason;
                stampMiss = ReceiptStampMiss(stamp.State);
                if (stamp.State == LeanCacheStampState.Match)
                {
                    try
                    {
                        LeanCacheProvisioner.VerifyMathlibOleans(lake);
                    }
                    catch (MathlibOleanCompletenessException exception)
                    {
                        return FailureReceipt(
                            "failed",
                            root,
                            donor: null,
                            method: "none",
                            pins.Sha256,
                            exception.Message,
                            exception.MissingOleanFiles,
                            exception.MissingOleanSamples,
                            pruneOutcome: exception.PruneOutcome);
                    }
                    return SuccessReceipt(
                        "present",
                        root,
                        donor: null,
                        method: "none",
                        pins.Sha256,
                        reason: null,
                        MathlibCachePruneOutcome.NotRun);
                }

                if (stamp.State == LeanCacheStampState.Mismatch)
                {
                    RemoveProjection(lake);
                }
                else
                {
                    // Missing or corrupt pin identity does not prove staleness. Re-run the current-pin
                    // producer and verify completeness in place. The new stamp records only pin
                    // identity; live completeness remains mandatory on every later admission.
                    try
                    {
                        var reproduced = LeanCacheProvisioner.ReproduceExisting(
                            root,
                            pins,
                            lakeExecutable,
                            runner,
                            writerGuard,
                            countLtarFiles);
                        return SuccessReceipt(
                            "fetched",
                            root,
                            donor: null,
                            reproduced.Method,
                            pins.Sha256,
                            JoinReasons(missReason, reproduced.Warning),
                            reproduced.PruneOutcome,
                            stampMiss);
                    }
                    catch (MathlibOleanCompletenessException exception)
                    {
                        if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
                        return FailureReceipt(
                            "failed",
                            root,
                            donor: null,
                            method: "cache-get",
                            pins.Sha256,
                            JoinReasons(missReason, exception.Message)
                                ?? "unknown in-place producer failure",
                            exception.MissingOleanFiles,
                            exception.MissingOleanSamples,
                            stampMiss,
                            exception.PruneOutcome);
                    }
                    catch (LeanCacheProvisionException exception)
                    {
                        if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
                        return FailureReceipt(
                            "failed",
                            root,
                            donor: null,
                            method: "cache-get",
                            pins.Sha256,
                            JoinReasons(missReason, exception.Message)
                                ?? "unknown in-place producer failure",
                            stampMiss: stampMiss,
                            pruneOutcome: exception.PruneOutcome);
                    }
                    catch (Exception exception)
                    {
                        if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
                        return FailureReceipt(
                            "failed",
                            root,
                            donor: null,
                            method: "cache-get",
                            pins.Sha256,
                            JoinReasons(missReason, exception.Message)
                                ?? "unknown in-place producer failure",
                            stampMiss: stampMiss);
                    }
                }
            }
            else if (File.Exists(lake))
            {
                stampMiss = "corrupt";
                return FailureReceipt(
                    "failed",
                    root,
                    donor: null,
                    method: "none",
                    pins.Sha256,
                    ".lake exists but is not a directory",
                    stampMiss: stampMiss);
            }

            using var selection = GitWorktreeInventory.SelectDonor(root, pins, runner);
            try
            {
                var provisioned = removePartial is null
                    ? LeanCacheProvisioner.Provision(
                        selection,
                        root,
                        pins,
                        lakeExecutable,
                        runner,
                        writerGuard,
                        cloner)
                    : LeanCacheProvisioner.Provision(
                        selection,
                        root,
                        pins,
                        lakeExecutable,
                        runner,
                        writerGuard,
                        cloner,
                        removePartial);
                return SuccessReceipt(
                    provisioned.Strategy == "cloned" ? "seeded" : "fetched",
                    root,
                    selection.Donor,
                    provisioned.Method,
                    pins.Sha256,
                    JoinReasons(missReason, JoinReasons(selection.Notice, provisioned.Warning)),
                    provisioned.PruneOutcome,
                    stampMiss,
                    provisioned.Clonefile);
            }
            catch (MathlibOleanCompletenessException exception)
            {
                if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
                return FailureReceipt(
                    "failed",
                    root,
                    selection.Donor,
                    "none",
                    pins.Sha256,
                    JoinReasons(missReason, JoinReasons(selection.Notice, exception.Message))
                        ?? "unknown provisioning failure",
                    exception.MissingOleanFiles,
                    exception.MissingOleanSamples,
                    stampMiss,
                    exception.PruneOutcome,
                    exception.Clonefile);
            }
            catch (LeanCacheProvisionException exception)
            {
                if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
                return FailureReceipt(
                    "failed",
                    root,
                    selection.Donor,
                    "none",
                    pins.Sha256,
                    JoinReasons(missReason, JoinReasons(selection.Notice, exception.Message))
                        ?? "unknown provisioning failure",
                    stampMiss: stampMiss,
                    pruneOutcome: exception.PruneOutcome,
                    clonefile: exception.Clonefile);
            }
            catch (Exception exception)
            {
                if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
                return FailureReceipt(
                    "failed",
                    root,
                    selection.Donor,
                    "none",
                    pins.Sha256,
                    JoinReasons(missReason, JoinReasons(selection.Notice, exception.Message))
                        ?? "unknown provisioning failure",
                    stampMiss: stampMiss);
            }
        }
        catch (Exception exception)
        {
            return FailureReceipt(
                "failed",
                root,
                donor: null,
                method: "none",
                pins.Sha256,
                exception.Message,
                stampMiss: stampMiss);
        }
    }

    private static CommandResult SuccessReceipt(
        string status,
        string worktree,
        string? donor,
        string method,
        string? pinSha256,
        string? reason,
        MathlibCachePruneOutcome pruneOutcome,
        string? stampMiss = null,
        ClonefileReceipt? clonefile = null) =>
        new(
            true,
            RenderReceipt(
                status,
                worktree,
                donor,
                method,
                pinSha256,
                reason,
                pruneOutcome,
                mathlibMissingOleanFiles: null,
                mathlibMissingOleanSamples: null,
                stampMiss,
                clonefile),
            string.Empty);

    private static CommandResult FailureReceipt(
        string status,
        string worktree,
        string? donor,
        string method,
        string? pinSha256,
        string reason,
        int? mathlibMissingOleanFiles = null,
        IReadOnlyList<string>? mathlibMissingOleanSamples = null,
        string? stampMiss = null,
        MathlibCachePruneOutcome? pruneOutcome = null,
        ClonefileReceipt? clonefile = null) =>
        new(
            false,
            string.Empty,
            RenderReceipt(
                status,
                worktree,
                donor,
                method,
                pinSha256,
                reason,
                pruneOutcome ?? MathlibCachePruneOutcome.NotRun,
                mathlibMissingOleanFiles,
                mathlibMissingOleanSamples,
                stampMiss,
                clonefile));

    private static CommandResult RefusedSymlink(string root, string pinSha256) =>
        FailureReceipt(
            "refused",
            root,
            donor: null,
            method: "none",
            pinSha256,
            reason: ".lake is a symlink; shared Lean caches are forbidden");

    private static bool TryParseWorktreeRoot(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        out string root)
    {
        var path = repositoryRoot;
        if (arguments.Count != 0)
        {
            if (arguments.Count != 2
                || !string.Equals(arguments[0], "--path", StringComparison.Ordinal)
                || string.IsNullOrWhiteSpace(arguments[1]))
            {
                root = string.Empty;
                return false;
            }

            path = arguments[1];
        }

        root = Path.GetFullPath(path);
        return true;
    }

    private static string RenderReceipt(
        string status,
        string worktree,
        string? donor,
        string method,
        string? pinSha256,
        string? reason,
        MathlibCachePruneOutcome pruneOutcome,
        int? mathlibMissingOleanFiles,
        IReadOnlyList<string>? mathlibMissingOleanSamples,
        string? stampMiss,
        ClonefileReceipt? clonefile = null) =>
        "LEAN_CACHE " + JsonSerializer.Serialize(new
        {
            status,
            worktree,
            donor,
            method,
            reason,
            stamp_miss = stampMiss,
            pin_sha256 = pinSha256,
            clonefile_errno = (clonefile ?? ClonefileReceipt.NotRun).LastErrno,
            clonefile_errnos = (clonefile ?? ClonefileReceipt.NotRun).Errnos,
            clonefile_attempts = (clonefile ?? ClonefileReceipt.NotRun).Attempts,
            clonefile_cleanup_error = (clonefile ?? ClonefileReceipt.NotRun).CleanupError,
            shared_cache_scope = pruneOutcome.Scope,
            mathlib_cache_pruned_files = pruneOutcome.DeletedFiles,
            mathlib_cache_clean_status = pruneOutcome.CleanStatus,
            mathlib_missing_olean_files = mathlibMissingOleanFiles,
            mathlib_missing_olean_samples = mathlibMissingOleanSamples,
        }) + "\n";

    private static bool TryParseWriter(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        out string root,
        out string[] command)
    {
        var index = 0;
        root = Path.GetFullPath(repositoryRoot);
        if (arguments.Count >= 2 && arguments[0] == "--path")
        {
            root = Path.GetFullPath(arguments[1]);
            index = 2;
        }
        if (index >= arguments.Count || arguments[index] != "--" || index + 1 >= arguments.Count)
        {
            command = [];
            return false;
        }
        command = arguments.Skip(index + 1).ToArray();
        return true;
    }

    private static string? JoinReasons(string? first, string? second)
    {
        if (string.IsNullOrWhiteSpace(first)) return second;
        if (string.IsNullOrWhiteSpace(second)) return first;
        return first + "; " + second;
    }

    private static string? ReceiptStampMiss(LeanCacheStampState state) => state switch
    {
        LeanCacheStampState.Missing => "missing",
        LeanCacheStampState.Corrupt => "corrupt",
        LeanCacheStampState.Mismatch => "mismatch",
        _ => null,
    };

    private static bool IsSymlink(string path) =>
        (Directory.Exists(path) || File.Exists(path))
        && File.GetAttributes(path).HasFlag(FileAttributes.ReparsePoint);

    private static void RemoveProjection(string lake) => Directory.Delete(lake, recursive: true);

}
