using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Cli;

internal sealed record CleanLanesOptions(string Base, bool Force, bool LanesOnly);

internal static class CleanLanesCommand
{
    internal const string Usage = "USAGE: StrataLint clean-lanes [--base REV] [--force] [--lanes-only]";

    internal static string BoundedDiagnostic(string value, int limit = 4096) =>
        value.Length <= limit ? value : value[..(limit / 2)] + "...[truncated]..." + value[(value.Length - limit / 2)..];

    internal static string? CanonicalRefusal(CommandResult result) =>
        result.Error.StartsWith("WORKTREE_RETAINED ", StringComparison.Ordinal)
            ? result.Error["WORKTREE_RETAINED ".Length..].Trim() : null;

    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments, DateTimeOffset now)
    {
        var caller = Directory.GetCurrentDirectory();
        try { return Run(repositoryRoot, arguments, new ProductionWorktreeProcessRunner(), [], now, Directory.SetCurrentDirectory); }
        finally { if (Directory.Exists(caller)) Directory.SetCurrentDirectory(caller); }
    }

    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner, IReadOnlyList<string> tempRoots, DateTimeOffset now, Action<string>? anchorProcess = null)
    {
        _ = tempRoots; _ = now;
        try
        {
            var options = ParseArguments(arguments);
            var inventory = RegisteredWorktreeInventory.ReadWorktrees(repositoryRoot, runner, resolveGitDirectories: false);
            if (inventory.Count == 0) throw new InvalidOperationException("git worktree inventory is empty");
            var root = inventory[0].Path;
            anchorProcess?.Invoke(root);
            var dev = RunGit(root, ["rev-parse", "--verify", "refs/remotes/origin/dev^{commit}"], runner, "origin/dev is unavailable");
            var args = new List<string> { "pool", "--dev", Decode(dev.StandardOutput).Trim() };
            if (options.Force) args.Add("--force");
            var result = WorktreeProtocolCommand.Run(root, args, runner, Timeout.InfiniteTimeSpan);
            if (result.Output.Length == 0) return result;
            using var document = JsonDocument.Parse(result.Output);
            var output = new StringBuilder();
            var failed = false;
            foreach (var row in document.RootElement.GetProperty("items").EnumerateArray())
            {
                var outcome = row.GetProperty("outcome").GetString()!;
                var action = outcome switch { "removed" => "removed", "would_remove" => "would_remove", "failed" => "failed", _ => "skipped" };
                failed |= action == "failed";
                output.AppendLine(JsonSerializer.Serialize(new
                {
                    @event = "clean_lanes_item", kind = "stale_worktree",
                    path = row.GetProperty("path").GetString(),
                    branch = row.TryGetProperty("branch", out var branch) ? branch.GetString() : null,
                    head = row.TryGetProperty("head", out var head) ? head.GetString() : null,
                    action, reason = row.TryGetProperty("reason", out var reason) ? reason.GetString() : null,
                }));
            }
            output.AppendLine(JsonSerializer.Serialize(new
            {
                @event = "clean_lanes_summary", status = failed ? "failed" : "succeeded",
                mode = options.Force ? "force" : "dry_run", scope = options.LanesOnly ? "lanes_only" : "full",
                item_count = document.RootElement.GetProperty("items").GetArrayLength(), base_revision = options.Base,
            }));
            return new CommandResult(!failed && result.Success, output.ToString(), result.Error, failed ? 74 : result.ExitCode);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        { return new CommandResult(false, string.Empty, $"CLEAN_LANES_FAILED {exception.Message}\n", 74); }
    }

    internal static CleanLanesOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        var baseRevision = "origin/dev"; var force = false; var lanesOnly = false;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--force" when !force: force = true; break;
                case "--lanes-only" when !lanesOnly: lanesOnly = true; break;
                case "--base" when index + 1 < arguments.Count && arguments[++index].Length > 0: baseRevision = arguments[index]; break;
                default: throw new InvalidOperationException(Usage);
            }
        }
        return new CleanLanesOptions(baseRevision, force, lanesOnly);
    }

    internal static ProcessOutput RunGit(string root, IReadOnlyList<string> arguments, IWorktreeProcessRunner runner, string fallback)
    {
        var result = runner.Run("git", arguments, root, BoundedProcessRunner.HangDetectionBudget);
        if (result.ExitCode != 0)
        {
            var error = Encoding.UTF8.GetString(result.StandardError).Trim();
            throw new InvalidOperationException(error.Length == 0 ? fallback : error);
        }
        return result;
    }

    internal static string Decode(byte[] bytes) => Encoding.UTF8.GetString(bytes);
}
