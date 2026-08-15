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
        IWorktreeProcessRunner runner) =>
        Run(repositoryRoot, arguments, runner, new ApfsDirectoryCloner());

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);
        ArgumentNullException.ThrowIfNull(cloner);
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

        var lake = Path.Combine(root, ".lake");
        using var guard = LeanCacheGuard.TryAcquireExclusive(lake);
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

        return EnsureLocked(root, pins, runner, cloner);
    }

    internal static CommandResult RunWithWriter(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner) =>
        RunWithWriter(repositoryRoot, arguments, runner, new ApfsDirectoryCloner());

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

        using var guard = LeanCacheGuard.TryAcquireExclusive(Path.Combine(root, ".lake"));
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

        var ensured = EnsureLocked(root, pins, runner, cloner);
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
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner)
    {
        var lake = Path.Combine(root, ".lake");
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
                    return SuccessReceipt(
                        "present",
                        root,
                        donor: null,
                        method: "none",
                        pins.Sha256,
                        reason: null,
                        mathlibCachePrunedFiles: null);
                }

                if (stamp.State == LeanCacheStampState.Mismatch)
                {
                    RemoveProjection(lake);
                }
                else
                {
                    // Missing or corrupt provenance does not prove staleness. Re-run the current-pin
                    // producer and verify completeness in place; the new stamp attests this run, so
                    // no existing byte is accepted without a successful producer invocation.
                    try
                    {
                        var reproduced = LeanCacheProvisioner.ReproduceExisting(root, pins, runner);
                        return SuccessReceipt(
                            "fetched",
                            root,
                            donor: null,
                            reproduced.Method,
                            pins.Sha256,
                            JoinReasons(missReason, reproduced.Warning),
                            reproduced.MathlibCachePrunedFiles,
                            stampMiss);
                    }
                    catch (Exception exception)
                    {
                        if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
                        missReason = JoinReasons(
                            missReason,
                            $"in-place current-pin producer failed ({exception.Message}); "
                            + "discarded the existing .lake before fresh provisioning");
                        RemoveProjectionIfPresent(lake);
                    }
                }
            }
            else if (File.Exists(lake))
            {
                missReason = ".lake exists but is not a directory";
                File.Delete(lake);
            }

            using var selection = GitWorktreeInventory.SelectDonor(root, pins, runner);
            try
            {
                var provisioned = LeanCacheProvisioner.Provision(
                    selection,
                    root,
                    pins,
                    runner,
                    cloner);
                return SuccessReceipt(
                    provisioned.Strategy == "cloned" ? "seeded" : "fetched",
                    root,
                    selection.Donor,
                    provisioned.Method,
                    pins.Sha256,
                    JoinReasons(missReason, JoinReasons(selection.Notice, provisioned.Warning)),
                    provisioned.MathlibCachePrunedFiles,
                    stampMiss);
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
                    stampMiss);
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
        int? mathlibCachePrunedFiles,
        string? stampMiss = null) =>
        new(
            true,
            RenderReceipt(
                status,
                worktree,
                donor,
                method,
                pinSha256,
                reason,
                mathlibCachePrunedFiles,
                mathlibMissingOleanFiles: null,
                mathlibMissingOleanSamples: null,
                stampMiss),
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
        string? stampMiss = null) =>
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
                mathlibCachePrunedFiles: null,
                mathlibMissingOleanFiles,
                mathlibMissingOleanSamples,
                stampMiss));

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
        int? mathlibCachePrunedFiles,
        int? mathlibMissingOleanFiles,
        IReadOnlyList<string>? mathlibMissingOleanSamples,
        string? stampMiss) =>
        "LEAN_CACHE " + JsonSerializer.Serialize(new
        {
            status,
            worktree,
            donor,
            method,
            reason,
            stamp_miss = stampMiss,
            pin_sha256 = pinSha256,
            shared_cache_scope = "machine",
            mathlib_cache_pruned_files = mathlibCachePrunedFiles,
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

    private static void RemoveProjectionIfPresent(string lake)
    {
        if (Directory.Exists(lake)) RemoveProjection(lake);
        else if (File.Exists(lake)) File.Delete(lake);
    }
}
