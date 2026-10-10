using System.Text;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Cli;

internal static class WorktreeProtocolCommand
{
    internal static CommandResult Run(string root, IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner, TimeSpan? timeout = null)
    {
        var script = FindScript(root);
        var result = runner.Run("python3", new[] { "-B", script, "--source", root }.Concat(arguments).ToArray(),
            root, timeout ?? BoundedProcessRunner.HangDetectionBudget);
        return new CommandResult(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput),
            Encoding.UTF8.GetString(result.StandardError), result.ExitCode);
    }

    private static string FindScript(string root)
    {
        foreach (var start in new[] { root, AppContext.BaseDirectory })
        {
            for (var directory = new DirectoryInfo(start); directory is not null; directory = directory.Parent)
            {
                var script = Path.Combine(directory.FullName, "tools/scripts/worktree/worktree_protocol.py");
                if (File.Exists(script)) return script;
            }
        }
        throw new InvalidOperationException("worktree protocol adapter is unavailable");
    }
}
