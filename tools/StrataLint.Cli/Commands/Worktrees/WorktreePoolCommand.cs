using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Cli;

internal static class WorktreePoolCommand
{
    internal const string IdlePrefix = "lane/governance/idle-";

    internal static CommandResult? TryClaim(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        if (options.PreferIdle)
        {
            var attached = RegisteredWorktreeInventory.ReadWorktrees(options.Source, runner,
                resolveGitDirectories: false).SingleOrDefault(item => item.Branch == options.Branch);
            if (attached is not null)
                return WorktreeProtocolCommand.Run(options.Source,
                    ["reuse", "--path", attached.Path, "--branch", options.Branch, "--base", options.Base], runner);
        }
        else
        {
            if (!Directory.Exists(options.Path)) return null;
            var attached = runner.Run("git", ["branch", "--show-current"], options.Path,
                BoundedProcessRunner.HangDetectionBudget);
            if (attached.ExitCode != 0 || !Encoding.UTF8.GetString(attached.StandardOutput).Trim()
                .StartsWith(IdlePrefix, StringComparison.Ordinal)) return null;
        }
        GitWorktreeInventory.FetchRemoteBase(options.Source, options.Base, runner);
        var arguments = new List<string> { "claim", "--branch", options.Branch, "--base", options.Base };
        if (!options.PreferIdle) arguments.AddRange(["--path", options.Path]);
        if (options.SkipRestore) arguments.Add("--skip-restore");
        var result = WorktreeProtocolCommand.Run(options.Source, arguments, runner, Timeout.InfiniteTimeSpan);
        if (!result.Success) return result;
        using var receipt = JsonDocument.Parse(result.Output);
        return receipt.RootElement.GetProperty("status").GetString() == "no_idle" ? null : result;
    }
}
