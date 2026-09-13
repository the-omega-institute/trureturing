using System.Text;
using System.Text.Json;

namespace StrataLint.EngineeringScope;

internal static class LeanCacheEnsureCommand
{
    internal const string Usage = "USAGE: StrataLint worktree ensure-cache [--path DIR]";
    internal const string ReaderUsage =
        "USAGE: StrataLint worktree with-cache-reader [--path DIR] -- COMMAND [ARG ...]";

    internal static CommandResult RunGit(string repositoryRoot, IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner)
    {
        if (!TryParse(repositoryRoot, arguments, true, out var root, out var gitArguments))
            return new(false, string.Empty, "USAGE: StrataLint worktree cache-git [--path DIR] -- ARG [ARG ...]\n");
        try
        {
            var result = LeanProcessPolicy.RunGit(root, runner, gitArguments);
            return new(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput),
                Encoding.UTF8.GetString(result.StandardError), result.ExitCode);
        }
        catch (Exception exception)
        {
            return new(false, string.Empty, "LEAN_CACHE_GIT " + exception.Message + "\n");
        }
    }

    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner, bool runCommand = false,
        Stream? standardOutput = null, Stream? standardError = null)
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
            if (standardOutput is not null)
            {
                standardOutput.Write(Encoding.UTF8.GetBytes(receipt));
                standardOutput.Flush();
            }
            var result = policy.Run(command[0], command.Skip(1).ToArray(), policy.Root,
                LeanCacheProvisioner.LeanCommandBudget, standardOutput, standardError);
            // Forwarded bytes have already reached their original stream; the bounded
            // captured result remains available to policy but must not be replayed.
            return new(result.ExitCode == 0,
                standardOutput is null ? receipt + Encoding.UTF8.GetString(result.StandardOutput) : string.Empty,
                standardError is null ? Encoding.UTF8.GetString(result.StandardError) : string.Empty, result.ExitCode);
        }
        catch (OperationCanceledException) { throw; }
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
