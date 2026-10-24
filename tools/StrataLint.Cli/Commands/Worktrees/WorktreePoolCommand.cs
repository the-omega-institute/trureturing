using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Cli;

internal static class WorktreePoolCommand
{
    internal const string IdlePrefix = "lane/governance/idle-";

    internal static bool IsIdleBranch(string? branch) =>
        branch is not null && branch.StartsWith(IdlePrefix, StringComparison.Ordinal)
            && branch.Length > IdlePrefix.Length;

    internal static CommandResult? TryClaim(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        if (options.PreferIdle)
        {
            var attached = RegisteredWorktreeInventory.ReadWorktrees(options.Source, runner,
                resolveGitDirectories: false).SingleOrDefault(item => item.Branch == options.Branch);
            if (attached is not null)
            {
                var reused = WorktreeCommand.RecoverInitialization(options with { Path = attached.Path }, runner);
                if (reused.Success && LeanPinSet.TryReadWorktree(attached.Path, out var reason) is null)
                    throw new InvalidOperationException(reason);
                return reused;
            }
        }
        else
        {
            if (!Directory.Exists(options.Path)) return null;
            var attached = runner.Run("git", ["branch", "--show-current"], options.Path,
                BoundedProcessRunner.HangDetectionBudget);
            if (attached.ExitCode != 0 || !IsIdleBranch(Encoding.UTF8.GetString(attached.StandardOutput).Trim()))
                return null;
            if (Encoding.UTF8.GetString(attached.StandardOutput).Trim() == options.Branch) return null;
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
