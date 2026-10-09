using StrataLint.Runtime;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using static StrataLint.Cli.CleanLanesCommand;

namespace StrataLint.Cli;

internal static class RemoveWorktreesCommand
{
    internal const string Usage =
        "USAGE: StrataLint worktree remove --names \"NAME [NAME ...]\" [--force]\n"
        + "Names are complete final directory names of registered worktrees, matched exactly (Ordinal). "
        + "Separate names with whitespace; directory names containing whitespace are unsupported. "
        + "All names are resolved before any deletion; duplicates are removed once. "
        + "The main checkout and locked worktrees are refused; intentional and initialization locks retain their meanings.\n"
        + "Removal requires remote preservation, complete content/recovery inspection and continuous OS entry/cache exclusion. "
        + "The optional CLI --force disables the default 300-second removal timeout; inventory remains bounded. "
        + "It may appear before or after --names and does not override main checkout or lock protection. "
        + "Branch refs are retained. Execution failures are reported and remaining resolved trees are attempted; no rollback.\n"
        + "CLI exits: 0 success; 64 usage; 65 not_found; 66 ambiguous; 67 main_worktree; 68 locked; "
        + "69 inventory unavailable or empty; 73 preservation/use refusal; 74 execution failure. "
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
        string? requestedNames = null;
        var force = false;
        for (var index = 0; index < arguments.Count; index++)
        {
            if (arguments[index] == "--names" && requestedNames is null && index + 1 < arguments.Count)
                requestedNames = arguments[++index];
            else if (arguments[index] == "--force" && !force)
                force = true;
            else
                return Complete(64, [], Usage);
        }
        if (string.IsNullOrWhiteSpace(requestedNames))
            return Complete(64, [], Usage);

        var names = requestedNames.Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries)
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

        CommandResult removal;
        try
        {
            var request = new List<string> { "remove", "--names", string.Join(' ', names) };
            if (force) request.Add("--force");
            foreach (var item in items)
            {
                var observed = inventory.Single(entry => entry.Path == item.Path);
                request.Add("--expected");
                request.Add(JsonSerializer.Serialize(new
                {
                    path = observed.Path, head = observed.Head,
                    branch = observed.Branch is null ? null : "refs/heads/" + observed.Branch,
                }));
            }
            removal = WorktreeProtocolCommand.Run(repositoryRoot, request, runner, Timeout.InfiniteTimeSpan);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return Complete(74, items.Select(item => item with
            {
                Outcome = "failed", Error = exception.Message, ExitCode = 74,
            }).ToArray());
        }
        if (removal.ExitCode == 73)
            return Complete(73, items.Select(item => item with
            {
                Outcome = "preservation_refused", Error = removal.Error, ExitCode = 73,
            }).ToArray());
        try
        {
            using var document = JsonDocument.Parse(removal.Output);
            var outcomes = document.RootElement.GetProperty("items").EnumerateArray().ToArray();
            var resolved = items.Select(item =>
            {
                var outcome = outcomes.Single(entry => entry.GetProperty("path").GetString() == item.Path);
                return outcome.GetProperty("outcome").GetString() == "removed"
                    ? item with { Outcome = "removed" }
                    : item with { Outcome = "failed", ExitCode = 74,
                        Error = outcome.GetProperty("error").GetString() };
            }).ToArray();
            return Complete(resolved.Any(item => item.ExitCode != 0) ? 74 : 0, resolved);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return Complete(74, items.Select(item => item with
            {
                Outcome = "failed", Error = "removal result indeterminate: " + removal.Error + exception.Message, ExitCode = 74,
            }).ToArray());
        }
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
            return new(name, match.Path, "locked", "intentional or initialization lock is retained", 68);
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
