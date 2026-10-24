using System.Text.Json;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private static void InspectIdlePool(string root, string? dev, bool force,
        IReadOnlyList<RegisteredWorktree> inventory,
        ICollection<CleanLaneEvent> events, IWorktreeProcessRunner runner)
    {
        var idle = inventory.Where(item => item.Branch?.StartsWith(
            WorktreePoolCommand.IdlePrefix, StringComparison.Ordinal) == true).ToArray();
        if (idle.Length == 0) return;
        if (dev is null)
        {
            foreach (var item in idle) events.Add(BlockedWorktree(item, "dev_unknown"));
            return;
        }
        var arguments = new List<string> { "pool", "--dev", dev };
        if (force) arguments.Add("--force");
        var result = WorktreeProtocolCommand.Run(root, arguments, runner, Timeout.InfiniteTimeSpan);
        if (!result.Success)
        {
            foreach (var item in idle) events.Add(BlockedWorktree(item, "idle_pool_unavailable"));
            return;
        }
        using var document = JsonDocument.Parse(result.Output);
        foreach (var item in document.RootElement.GetProperty("items").EnumerateArray())
        {
            var outcome = item.GetProperty("outcome").GetString()!;
            events.Add(new CleanLaneEvent("idle_worktree", item.GetProperty("path").GetString(),
                item.GetProperty("branch").GetString()?.Replace("refs/heads/", string.Empty, StringComparison.Ordinal),
                item.GetProperty("head").GetString(), outcome == "retained" ? "skipped" : outcome,
                item.GetProperty("reason").GetString()!));
        }
    }
}
