using System.Globalization;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal enum WorktreeHoldOperation
{
    Hold,
    Release,
}

internal sealed record WorktreeHoldOptions(
    WorktreeHoldOperation Operation,
    string Path,
    string? Reason);

internal sealed record HeldWorktree(
    string Path,
    string? Branch,
    bool Locked,
    string? LockReason);

internal static class WorktreeHoldCommand
{
    private const string Usage =
        "USAGE: StrataLint worktree hold --path DIR [--reason TEXT] | "
        + "StrataLint worktree release --path DIR";
    private static readonly TimeSpan GitTimeout = TimeSpan.FromSeconds(30);

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        DateTimeOffset now)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);

        WorktreeHoldOptions options;
        try
        {
            options = ParseArguments(arguments);
        }
        catch (InvalidOperationException exception)
        {
            return Refused(
                RequestedOperation(arguments),
                null,
                null,
                null,
                "invalid_arguments",
                exception.Message);
        }

        ProcessOutput inventoryOutput;
        try
        {
            inventoryOutput = runner.Run(
                "git",
                ["worktree", "list", "--porcelain", "-z"],
                repositoryRoot,
                GitTimeout);
        }
        catch (Exception exception)
        {
            return Refused(
                OperationName(options.Operation),
                options.Path,
                null,
                null,
                "inventory_failed",
                exception.Message);
        }

        if (inventoryOutput.ExitCode != 0)
        {
            return Refused(
                OperationName(options.Operation),
                options.Path,
                null,
                null,
                "inventory_failed",
                ProcessError(inventoryOutput, "git worktree inventory failed"));
        }

        IReadOnlyList<HeldWorktree> inventory;
        try
        {
            inventory = ParseInventory(inventoryOutput.StandardOutput);
        }
        catch (InvalidOperationException exception)
        {
            return Refused(
                OperationName(options.Operation),
                options.Path,
                null,
                null,
                "inventory_malformed",
                exception.Message);
        }

        var lane = inventory.SingleOrDefault(item =>
            string.Equals(item.Path, options.Path, StringComparison.Ordinal));
        if (lane is null)
        {
            return Refused(
                OperationName(options.Operation),
                options.Path,
                null,
                null,
                "unregistered_worktree",
                "path is not registered in git worktree inventory");
        }

        var registeredLane = lane!;
        if (registeredLane.Branch is null
            || !WorktreeCommand.IsManagedBranch(registeredLane.Branch))
        {
            return Refused(
                OperationName(options.Operation),
                options.Path,
                registeredLane.Branch,
                registeredLane.LockReason,
                "not_managed_lane",
                "branch must match harness/* or agent/<official>/<task-code>");
        }

        if (options.Operation == WorktreeHoldOperation.Hold)
        {
            return Hold(repositoryRoot, options, registeredLane, runner, now);
        }

        return Release(repositoryRoot, options, registeredLane, runner);
    }

    internal static CommandResult Hold(
        string repositoryRoot,
        WorktreeHoldOptions options,
        HeldWorktree lane,
        IWorktreeProcessRunner runner,
        DateTimeOffset now)
    {
        if (lane.Locked)
        {
            return Succeeded(options, lane, "already_held", lane.LockReason);
        }

        var effectiveReason = FormatReason(now, options.Reason);
        ProcessOutput result;
        try
        {
            result = runner.Run(
                "git",
                ["worktree", "lock", "--reason", effectiveReason, lane.Path],
                repositoryRoot,
                GitTimeout);
        }
        catch (Exception exception)
        {
            return Refused(
                "hold",
                options.Path,
                lane.Branch,
                null,
                "lock_failed",
                exception.Message);
        }

        if (result.ExitCode != 0)
        {
            return Refused(
                "hold",
                options.Path,
                lane.Branch,
                null,
                "lock_failed",
                ProcessError(result, "git worktree lock failed"));
        }

        return Succeeded(options, lane, "held", effectiveReason);
    }

    private static CommandResult Release(
        string repositoryRoot,
        WorktreeHoldOptions options,
        HeldWorktree lane,
        IWorktreeProcessRunner runner)
    {
        if (!lane.Locked)
        {
            return Succeeded(options, lane, "already_released", null);
        }

        ProcessOutput result;
        try
        {
            result = runner.Run(
                "git",
                ["worktree", "unlock", lane.Path],
                repositoryRoot,
                GitTimeout);
        }
        catch (Exception exception)
        {
            return Refused(
                "release",
                options.Path,
                lane.Branch,
                lane.LockReason,
                "unlock_failed",
                exception.Message);
        }

        if (result.ExitCode != 0)
        {
            return Refused(
                "release",
                options.Path,
                lane.Branch,
                lane.LockReason,
                "unlock_failed",
                ProcessError(result, "git worktree unlock failed"));
        }

        return Succeeded(options, lane, "released", lane.LockReason);
    }

    private static WorktreeHoldOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 0) throw new InvalidOperationException(Usage);

        var operation = arguments[0] switch
        {
            "hold" => WorktreeHoldOperation.Hold,
            "release" => WorktreeHoldOperation.Release,
            _ => throw new InvalidOperationException(Usage),
        };
        string? path = null;
        string? reason = null;
        for (var index = 1; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--path" when path is null:
                    path = ReadValue(arguments, ref index);
                    break;
                case "--reason" when operation == WorktreeHoldOperation.Hold && reason is null:
                    reason = ReadValue(arguments, ref index);
                    break;
                default:
                    throw new InvalidOperationException(Usage);
            }
        }

        if (path is null) throw new InvalidOperationException(Usage);
        return new WorktreeHoldOptions(operation, NormalizePath(path!), reason);
    }

    private static string ReadValue(IReadOnlyList<string> arguments, ref int index)
    {
        if (++index >= arguments.Count || arguments[index].Length == 0)
        {
            throw new InvalidOperationException(Usage);
        }

        return arguments[index];
    }

    private static IReadOnlyList<HeldWorktree> ParseInventory(byte[] bytes)
    {
        var worktrees = new List<HeldWorktree>();
        string? path = null;
        string? branch = null;
        var locked = false;
        string? reason = null;

        void FinishRecord()
        {
            if (path is null) return;
            if (worktrees.Any(item => string.Equals(item.Path, path, StringComparison.Ordinal)))
            {
                throw new InvalidOperationException("git worktree inventory contains a duplicate path");
            }

            worktrees.Add(new HeldWorktree(path, branch, locked, reason));
            path = null;
            branch = null;
            locked = false;
            reason = null;
        }

        foreach (var field in Encoding.UTF8.GetString(bytes).Split('\0'))
        {
            if (field.Length == 0)
            {
                FinishRecord();
                continue;
            }

            if (field.StartsWith("worktree ", StringComparison.Ordinal))
            {
                if (path is not null)
                {
                    throw new InvalidOperationException("git worktree inventory omitted a record separator");
                }

                var value = field["worktree ".Length..];
                if (value.Length == 0)
                {
                    throw new InvalidOperationException("git worktree inventory contains an empty path");
                }

                path = NormalizePath(value);
                continue;
            }

            if (path is null)
            {
                throw new InvalidOperationException("git worktree inventory field precedes its path");
            }

            if (field.StartsWith("branch ", StringComparison.Ordinal))
            {
                if (branch is not null)
                {
                    throw new InvalidOperationException("git worktree inventory contains duplicate branches");
                }

                branch = field["branch ".Length..];
                const string headsPrefix = "refs/heads/";
                if (branch.StartsWith(headsPrefix, StringComparison.Ordinal))
                {
                    branch = branch[headsPrefix.Length..];
                }
            }
            else if (field == "locked")
            {
                locked = true;
            }
            else if (field.StartsWith("locked ", StringComparison.Ordinal))
            {
                locked = true;
                reason = field["locked ".Length..];
            }
        }

        FinishRecord();
        if (worktrees.Count == 0)
        {
            throw new InvalidOperationException("git worktree inventory is empty");
        }

        return worktrees;
    }

    private static string FormatReason(DateTimeOffset now, string? suppliedReason)
    {
        var effective = "held_at_utc=" + now.UtcDateTime.ToString(
            "yyyy-MM-dd'T'HH:mm:ss.fff'Z'",
            CultureInfo.InvariantCulture);
        if (!string.IsNullOrWhiteSpace(suppliedReason))
        {
            effective += "; reason=" + suppliedReason;
        }

        return effective;
    }

    private static CommandResult Succeeded(
        WorktreeHoldOptions options,
        HeldWorktree lane,
        string action,
        string? effectiveReason) =>
        Render(
            true,
            OperationName(options.Operation),
            options.Path,
            lane.Branch,
            action,
            effectiveReason,
            null,
            null);

    private static CommandResult Refused(
        string? operation,
        string? path,
        string? branch,
        string? effectiveReason,
        string error,
        string detail) =>
        Render(false, operation, path, branch, "refused", effectiveReason, error, detail);

    private static CommandResult Render(
        bool success,
        string? operation,
        string? path,
        string? branch,
        string action,
        string? effectiveReason,
        string? error,
        string? detail)
    {
        var line = JsonSerializer.Serialize(new
        {
            @event = "worktree_hold_state",
            path,
            branch,
            operation,
            action,
            effective_reason = effectiveReason,
            error,
            detail,
        }) + "\n";
        return success
            ? new CommandResult(true, line, string.Empty)
            : new CommandResult(false, string.Empty, line);
    }

    private static string? RequestedOperation(IReadOnlyList<string> arguments) =>
        arguments.Count == 0 ? null : arguments[0];

    private static string OperationName(WorktreeHoldOperation operation) =>
        operation == WorktreeHoldOperation.Hold ? "hold" : "release";

    private static string NormalizePath(string value) =>
        System.IO.Path.TrimEndingDirectorySeparator(System.IO.Path.GetFullPath(value));

    private static string ProcessError(ProcessOutput output, string fallback)
    {
        var error = Encoding.UTF8.GetString(output.StandardError).Trim();
        return error.Length == 0 ? fallback : error;
    }
}
