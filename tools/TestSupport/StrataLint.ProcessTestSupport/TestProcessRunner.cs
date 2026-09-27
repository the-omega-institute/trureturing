using StrataLint.Engine;
using Xunit;

namespace StrataLint.TestSupport;

internal static class TestProcessRunner
{
    internal static ProcessOutput Run(
        string fileName,
        IEnumerable<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        int maximumOutputBytes,
        ReadOnlyMemory<byte> standardInput = default,
        Stream? standardOutput = null,
        Stream? standardError = null) =>
        Classify(
            () => BoundedProcessRunner.Run(
                fileName,
                arguments,
                workingDirectory,
                timeout,
                maximumOutputBytes,
                standardInput,
                standardOutput: standardOutput,
                standardError: standardError),
            fileName);

    internal static ProcessOutput Classify(Func<ProcessOutput> run, string command) =>
        Classify<ProcessOutput>(run, command);

    internal static T Classify<T>(Func<T> run, string command)
    {
        try
        {
            return run();
        }
        catch (TimeoutException exception)
        {
            throw new SkipException(
                $"{InfrastructureHangGuard.SkipReasonPrefix} for {command}: {exception.Message}");
        }
    }
}
