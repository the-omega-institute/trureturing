using StrataLint.Engine;

namespace StrataLint.Cli;

internal interface IWorktreeProcessRunner
{
    ProcessOutput Run(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout);

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

internal sealed class ProductionWorktreeProcessRunner : IWorktreeProcessRunner
{
    public StreamedProcessOutput<T> RunStreaming<T>(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        Func<Stream, CancellationToken, Task<T>> readStandardOutput) =>
        BoundedProcessRunner.RunStreaming(fileName, arguments, workingDirectory, timeout,
            64 * 1024 * 1024, readStandardOutput);

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
            64 * 1024 * 1024);
}
