using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Cli;

internal static class WorktreePoolCommand
{
    internal static CommandResult? TryReuse(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        GitWorktreeInventory.FetchRemoteBase(options.Source, options.Base, runner);
        var arguments = new List<string> { "claim", "--branch", options.Branch, "--base", options.Base };
        if (options.SkipRestore) arguments.Add("--skip-restore");
        var result = WorktreeProtocolCommand.Run(options.Source, arguments, runner, Timeout.InfiniteTimeSpan);
        if (!result.Success) return result;
        using var receipt = JsonDocument.Parse(result.Output);
        return receipt.RootElement.GetProperty("status").GetString() == "no_reusable"
            ? null
            : result;
    }
}
