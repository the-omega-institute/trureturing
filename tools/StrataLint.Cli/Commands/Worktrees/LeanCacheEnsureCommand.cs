using System.Text;
using System.Text.Json;

namespace StrataLint.Cli;

internal static class LeanCacheEnsureCommand
{
    internal const string Usage = "USAGE: StrataLint worktree ensure-cache [--path DIR]";
    internal const string ReaderUsage =
        "USAGE: StrataLint worktree with-cache-reader [--path DIR] -- COMMAND [ARG ...]";

    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner, bool runCommand = false)
    {
        if (!TryParse(repositoryRoot, arguments, runCommand, out var root, out var command))
            return new(false, string.Empty, (runCommand ? ReaderUsage : Usage) + "\n");
        try
        {
            var pins = LeanPinSet.TryReadWorktree(root, out var reason)
                ?? throw new InvalidOperationException(reason);
            LeanCacheProvisioner.RequirePrivateLake(root);
            var policy = LeanProcessPolicy.Create(root, pins, runner);
            using var guard = LeanCacheWriterGuard.TryAcquire(Path.Combine(policy.Root, ".lake"), policy.LockDirectory)
                ?? throw new InvalidOperationException("private .lake writer guard is busy");
            policy.Writers = [guard];
            var receipt = LeanCacheProvisioner.Ensure(policy, pins, guard);
            if (!runCommand) return new(true, receipt, string.Empty);
            var result = policy.Run(command[0], command.Skip(1).ToArray(), policy.Root,
                LeanCacheProvisioner.LeanCommandBudget);
            return new(result.ExitCode == 0, receipt + Encoding.UTF8.GetString(result.StandardOutput),
                Encoding.UTF8.GetString(result.StandardError), result.ExitCode);
        }
        catch (Exception exception)
        {
            return new(false, string.Empty, "LEAN_CACHE " + JsonSerializer.Serialize(new
            {
                status = "failed", worktree = root, reason = exception.Message,
            }) + "\n");
        }
    }

    internal static bool TryParse(string repositoryRoot, IReadOnlyList<string> arguments,
        bool runCommand, out string root, out string[] command)
    {
        root = Path.GetFullPath(repositoryRoot);
        command = [];
        var index = 0;
        if (arguments.Count >= 2 && arguments[0] == "--path")
        {
            root = Path.GetFullPath(arguments[1]);
            index = 2;
        }
        if (!runCommand) return index == arguments.Count;
        if (index >= arguments.Count || arguments[index] != "--" || index + 1 == arguments.Count)
            return false;
        command = arguments.Skip(index + 1).ToArray();
        return true;
    }
}
