using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using static StrataLint.Cli.CleanLanesCommand;

namespace StrataLint.Cli;

internal static class RemoveWorktreesCommand
{
    internal const string Usage =
        "USAGE: StrataLint worktree remove --names \"NAME [NAME ...]\"\n"
        + "Names are complete final directory names of registered worktrees, matched exactly (Ordinal). "
        + "Separate names with whitespace; directory names containing whitespace are unsupported. "
        + "All names are resolved before any deletion; duplicates are removed once. "
        + "The main checkout and locked worktrees are refused; first run git worktree unlock <path> for a locked tree.\n"
        + "Removal uses one --force, bypassing unmerged, dirty, age, open PR and process occupancy criteria. "
        + "Branch refs are retained. Execution failures are reported and remaining resolved trees are attempted; no rollback.\n"
        + "CLI exits: 0 success; 64 usage; 65 not_found; 66 ambiguous; 67 main_worktree; 68 locked; "
        + "69 inventory unavailable or empty; 74 execution failure. "
        + "GNU make returns its own 0/2; read the final WORKTREE_REMOVE_RESULT line for the classified exit.\n";

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);
        if (arguments.Count == 1 && arguments[0] is "--help" or "-h")
            return Complete(0, [], Usage);
        if (arguments.Count != 2 || arguments[0] != "--names" || string.IsNullOrWhiteSpace(arguments[1]))
            return Complete(64, [], Usage);

        var names = arguments[1].Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries)
            .Distinct(StringComparer.Ordinal).ToArray();
        IReadOnlyList<RegisteredWorktree> inventory;
        try
        {
            inventory = RegisteredWorktreeInventory.ReadWorktrees(
                Path.GetFullPath(repositoryRoot), runner, resolveGitDirectories: false);
            if (inventory.Count == 0) throw new InvalidOperationException("git worktree inventory is empty");
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return Complete(69, names.Select(name =>
                new RemovalItem(name, null, "inventory_unavailable", exception.Message, 69)).ToArray());
        }

        // Git lists the main checkout first. It must remain in the matching set.
        var mainPath = inventory[0].Path;
        var items = names.Select(name => Resolve(name, inventory, mainPath)).ToArray();
        var firstRefusal = items.FirstOrDefault(static item => item.ExitCode != 0);
        if (firstRefusal is not null)
        {
            return Complete(firstRefusal.ExitCode, items.Select(static item => item.ExitCode == 0
                ? item with { Outcome = "batch_refused", Error = "another name in the batch was refused" }
                : item).ToArray());
        }

        for (var index = 0; index < items.Length; index++)
        {
            var item = items[index];
            try
            {
                var result = runner.Run("git", ["worktree", "remove", "--force", "--", item.Path!],
                    mainPath, BoundedProcessRunner.HangDetectionBudget);
                if (result.ExitCode == 0)
                {
                    items[index] = item with { Outcome = "removed" };
                }
                else
                {
                    var error = Decode(result.StandardError);
                    items[index] = item with
                    {
                        Outcome = "failed",
                        Error = error.Length == 0 ? $"git worktree remove exited {result.ExitCode}" : error,
                        ExitCode = 74,
                    };
                }
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                items[index] = item with { Outcome = "failed", Error = exception.Message, ExitCode = 74 };
            }
        }

        return Complete(items.Any(static item => item.Outcome == "failed") ? 74 : 0, items);
    }

    private static RemovalItem Resolve(string name, IReadOnlyList<RegisteredWorktree> inventory, string mainPath)
    {
        var matches = inventory.Where(item => string.Equals(
            Path.GetFileName(Path.TrimEndingDirectorySeparator(item.Path)), name, StringComparison.Ordinal)).ToArray();
        if (matches.Length == 0)
            return new(name, null, "not_found", "no registered worktree has this directory name", 65);
        if (matches.Length > 1)
        {
            return new(name, null, "ambiguous", "matches multiple registered paths: "
                + string.Join(", ", matches.Select(static item => item.Path)), 66);
        }

        var match = matches[0];
        if (string.Equals(match.Path, mainPath, StringComparison.Ordinal))
        {
            return new(name, match.Path, "main_worktree", "the main checkout cannot be removed", 67);
        }
        if (match.Locked)
            return new(name, match.Path, "locked", "first run git worktree unlock <path>", 68);
        return new(name, match.Path, "resolved", null, 0);
    }

    private static CommandResult Complete(int exit, IReadOnlyList<RemovalItem> items, string prefix = "")
    {
        var output = new StringBuilder(prefix);
        foreach (var item in items)
        {
            output.AppendLine(JsonSerializer.Serialize(new
            {
                name = item.Name,
                path = item.Path,
                outcome = item.Outcome,
                error = item.Error,
            }));
        }
        var removed = items.Count(static item => item.Outcome == "removed");
        var failed = items.Count(static item => item.Outcome == "failed");
        output.Append($"WORKTREE_REMOVE_RESULT exit={exit} removed={removed} failed={failed} refused={items.Count - removed - failed}\n");
        return new CommandResult(exit == 0, output.ToString(), string.Empty, exit);
    }

    private sealed record RemovalItem(string Name, string? Path, string Outcome, string? Error, int ExitCode);
}
