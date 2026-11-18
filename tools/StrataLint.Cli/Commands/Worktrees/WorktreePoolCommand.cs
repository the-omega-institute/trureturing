using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Cli;

internal static class WorktreePoolCommand
{
    internal static CommandResult PrepareAllocation(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        var arguments = new List<string> { "claim", "--branch", options.Branch, "--base", options.Base };
        if (options.AllowReuseSelection) arguments.AddRange(["--initializing-path", options.Path]);
        if (!options.AllowReuseSelection) arguments.AddRange(["--path", options.Path]);
        if (options.SkipRestore) arguments.Add("--skip-restore");
        var result = WorktreeProtocolCommand.Run(options.Source, arguments, runner, Timeout.InfiniteTimeSpan, reportPending: false);
        if (!result.Success) return result;
        using var receipt = JsonDocument.Parse(result.Output);
        if (receipt.RootElement.GetProperty("status").GetString() == "no_reusable") return result;
        var path = receipt.RootElement.GetProperty("path").GetString()
            ?? throw new InvalidOperationException("claimed worktree path is absent");
        if (LeanPinSet.TryReadWorktree(path, out var reason) is null)
            throw new InvalidOperationException(reason);
        return result;
    }
}
