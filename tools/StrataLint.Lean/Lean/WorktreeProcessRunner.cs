using StrataLint.Runtime;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal interface IWorktreeProcessRunner
{
    ProcessOutput Run(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout);

    ProcessOutput Run(
        string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan timeout,
        Stream? standardOutput, Stream? standardError) =>
        standardOutput is null && standardError is null
            ? Run(fileName, arguments, workingDirectory, timeout)
            : throw new NotSupportedException("This process runner does not support forwarding child output.");

    StreamedProcessOutput<T> RunStreaming<T>(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        Func<Stream, CancellationToken, Task<T>> readStandardOutput)
    {
        var result = Run(fileName, arguments, workingDirectory, timeout);
        using var stream = new MemoryStream(result.StandardOutput, writable: false);
        return new StreamedProcessOutput<T>(result.ExitCode,
            readStandardOutput(stream, CancellationToken.None).GetAwaiter().GetResult(), result.StandardError);
    }
}

internal sealed class ProductionWorktreeProcessRunner(CancellationToken cancellationToken = default) : IWorktreeProcessRunner
{
    public ProcessOutput Run(
        string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan timeout,
        Stream? standardOutput, Stream? standardError) =>
        BoundedProcessRunner.Run(fileName, arguments, workingDirectory, timeout,
            64 * 1024 * 1024, standardOutput: standardOutput, standardError: standardError,
            environment: GitEnvironment(fileName), cancellationToken: cancellationToken);

    public StreamedProcessOutput<T> RunStreaming<T>(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        Func<Stream, CancellationToken, Task<T>> readStandardOutput) =>
        BoundedProcessRunner.RunStreaming(fileName, arguments, workingDirectory, timeout,
            64 * 1024 * 1024, readStandardOutput, environment: GitEnvironment(fileName),
            cancellationToken: cancellationToken);

    public ProcessOutput Run(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout) =>
        BoundedProcessRunner.Run(
            fileName,
            arguments,
            workingDirectory,
            timeout,
            64 * 1024 * 1024, environment: GitEnvironment(fileName), cancellationToken: cancellationToken);

    private static IReadOnlyDictionary<string, string>? GitEnvironment(string fileName)
    {
        if (Path.GetFileName(fileName) != "git") return null;
        string[] permitted = ["GIT_SSH", "GIT_SSH_COMMAND", "GIT_SSH_VARIANT", "GIT_ASKPASS",
            "GIT_TERMINAL_PROMPT", "GIT_AUTHOR_NAME", "GIT_AUTHOR_EMAIL", "GIT_AUTHOR_DATE",
            "GIT_COMMITTER_NAME", "GIT_COMMITTER_EMAIL", "GIT_COMMITTER_DATE"];
        return Environment.GetEnvironmentVariables().Cast<System.Collections.DictionaryEntry>()
            .Where(entry => !((string)entry.Key).StartsWith("GIT_", StringComparison.Ordinal)
                || permitted.Contains((string)entry.Key, StringComparer.Ordinal))
            .ToDictionary(entry => (string)entry.Key, entry => (string)entry.Value!, StringComparer.Ordinal);
    }
}
