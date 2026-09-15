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
            cancellationToken: cancellationToken);

    public StreamedProcessOutput<T> RunStreaming<T>(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        Func<Stream, CancellationToken, Task<T>> readStandardOutput) =>
        BoundedProcessRunner.RunStreaming(fileName, arguments, workingDirectory, timeout,
            64 * 1024 * 1024, readStandardOutput, cancellationToken: cancellationToken);

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
            64 * 1024 * 1024, cancellationToken: cancellationToken);
}
