using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed class RecordingDirectoryCloner : IDirectoryCloner
{
    internal List<(string Source, string Target)> Invocations { get; } = [];
    internal string? FailureReason { get; init; }

    public DirectoryCloneResult Clone(string source, string target)
    {
        Invocations.Add((source, target));
        return FailureReason is null
            ? new ApfsDirectoryCloner().Clone(source, target)
            : new(false, null, FailureReason);
    }
}

internal sealed record WorktreeProcessInvocation(
    string FileName, IReadOnlyList<string> Arguments, string WorkingDirectory, TimeSpan Timeout);

internal sealed class RecordingWorktreeProcessRunner : IWorktreeProcessRunner
{
    internal List<WorktreeProcessInvocation> Invocations { get; } = [];
    internal bool FailDotnet { get; init; }
    internal bool FailWorktreeAdd { get; init; }
    internal Action<string>? AfterWorktreeAdd { get; init; }

    public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments,
        string workingDirectory, TimeSpan timeout)
    {
        Invocations.Add(new(fileName, arguments.ToArray(), workingDirectory, timeout));
        if (fileName == "git" && arguments.Take(2).SequenceEqual(["worktree", "add"]) && FailWorktreeAdd)
            return Failure("simulated concurrent worktree");
        if (fileName == "dotnet") return FailDotnet ? Failure("dotnet restore failed") : new(0, [], []);
        var result = TestProcessRunner.Run(fileName, arguments, workingDirectory, timeout, 64 * 1024 * 1024);
        if (fileName == "git" && arguments.Take(2).SequenceEqual(["worktree", "add"]) && result.ExitCode == 0)
            AfterWorktreeAdd?.Invoke(arguments[^2]);
        return result;
    }

    private static ProcessOutput Failure(string message) => new(1, [], Encoding.UTF8.GetBytes(message));
}

internal static class MathlibProjectionFixture
{
    private static readonly string[] Modules =
    [
        "Mathlib/Algebra/Basic",
        "Mathlib/Topology/Basic",
    ];

    internal static int ModuleCount => Modules.Length;

    internal static string FirstModule => Modules[0];

    internal static void Write(string lake, bool includeOleans = true)
    {
        var mathlib = Path.Combine(lake, "packages", "mathlib");
        foreach (var module in Modules)
        {
            var relative = module.Replace('/', Path.DirectorySeparatorChar);
            var source = Path.Combine(mathlib, relative + ".lean");
            Directory.CreateDirectory(Path.GetDirectoryName(source)!);
            File.WriteAllText(source, "-- fixture\n");
            if (!includeOleans) continue;

            var olean = Path.Combine(mathlib, ".lake", "build", "lib", "lean", relative + ".olean");
            Directory.CreateDirectory(Path.GetDirectoryName(olean)!);
            File.WriteAllText(olean, "fixture\n");
        }
    }

}

internal static class WorktreeHookFixture
{
    internal static string Install(string repository, string name, string body)
    {
        var hooks = Path.Combine(repository, ".git", "creation-hooks");
        Directory.CreateDirectory(hooks);
        RunGit(repository, "config", "core.hooksPath", hooks);
        var path = Path.Combine(hooks, name);
        File.WriteAllText(path, "#!/bin/sh\nset -eu\n" + body, new UTF8Encoding(false));
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        return path;
    }

    internal static string RunGit(string repository, params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, repository,
            BoundedProcessRunner.HangDetectionBudget, 64 * 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        return Encoding.UTF8.GetString(result.StandardOutput);
    }
}
