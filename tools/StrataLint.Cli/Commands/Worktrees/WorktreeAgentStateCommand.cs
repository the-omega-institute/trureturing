using System.Text;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Cli;

internal static class WorktreeAgentStateCommand
{
    // Only outer lifecycle entrances call this. Cache/build wrappers do not.
    internal static CommandResult After(string root, IWorktreeProcessRunner runner, Func<CommandResult> operation)
    {
        var anchor = root;
        var auxiliary = runner;
        try
        {
            if (runner is ProductionWorktreeProcessRunner production)
                auxiliary = production.WithEnvironment(WorktreeProtocolCommand.InitializationEnvironment(root, TimeSpan.FromSeconds(4)));
            var inventory = auxiliary.Run("git", ["worktree", "list", "--porcelain", "-z"], root, TimeSpan.FromSeconds(4));
            var first = Encoding.UTF8.GetString(inventory.StandardOutput).Split('\0')[0];
            if (inventory.ExitCode == 0 && first.StartsWith("worktree ", StringComparison.Ordinal))
                anchor = first["worktree ".Length..];
        }
        catch (Exception error) when (error is not OutOfMemoryException) { /* Final view reports unavailable data. */ }
        var result = operation();
        try
        {
            var pending = WorktreeProtocolCommand.Run(anchor, ["pending"], auxiliary, TimeSpan.FromSeconds(6));
            return result with { Error = result.Error + pending.Error + (!pending.Success || pending.Error.Length == 0
                ? "WORKTREE_AGENT_WARNING pending summary unavailable\n" : string.Empty) };
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            return result with { Error = result.Error + "WORKTREE_AGENT_WARNING pending summary unavailable: "
                + CleanLanesCommand.BoundedDiagnostic(error.Message, 512) + "\n" };
        }
    }

    internal static string Capture(string source, string path, string branch, IWorktreeProcessRunner runner)
    {
        try
        {
            var result = WorktreeProtocolCommand.Run(source, ["record-registration", "--path", path, "--branch", branch],
                runner, TimeSpan.FromSeconds(6), reportPending: false);
            return result.Error + (result.Success ? string.Empty : "WORKTREE_AGENT_WARNING attribution unavailable\n");
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            return "WORKTREE_AGENT_WARNING attribution unavailable: "
                + CleanLanesCommand.BoundedDiagnostic(error.Message, 512) + "\n";
        }
    }
}
