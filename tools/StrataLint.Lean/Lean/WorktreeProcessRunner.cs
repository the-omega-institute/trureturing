using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal interface IWorktreeProcessRunner
{
    ProcessOutput Run(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout);

    ProcessOutput RunWithEnvironment(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        IReadOnlyDictionary<string, string> environment) =>
        throw new NotSupportedException("This process runner does not support an isolated child environment.");

    ProcessOutput RunWithEnvironment(
        string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan timeout,
        IReadOnlyDictionary<string, string> environment, Stream? standardOutput, Stream? standardError) =>
        standardOutput is null && standardError is null
            ? RunWithEnvironment(fileName, arguments, workingDirectory, timeout, environment)
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
    public ProcessOutput RunWithEnvironment(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        IReadOnlyDictionary<string, string> environment) =>
        BoundedProcessRunner.Run(fileName, arguments, workingDirectory, timeout,
            64 * 1024 * 1024, environment: environment, cancellationToken: cancellationToken);

    public ProcessOutput RunWithEnvironment(
        string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan timeout,
        IReadOnlyDictionary<string, string> environment, Stream? standardOutput, Stream? standardError) =>
        BoundedProcessRunner.Run(fileName, arguments, workingDirectory, timeout,
            64 * 1024 * 1024, environment: environment, standardOutput: standardOutput,
            standardError: standardError, cancellationToken: cancellationToken);

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
