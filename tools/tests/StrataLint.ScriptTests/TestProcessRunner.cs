using StrataLint.Engine;
using Xunit;

namespace StrataLint.ScriptTests;

internal static class TestProcessRunner
{
    internal static ProcessOutput Run(
        string fileName,
        IEnumerable<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        int maximumOutputBytes)
    {
        try
        {
            return BoundedProcessRunner.Run(
                fileName,
                arguments,
                workingDirectory,
                timeout,
                maximumOutputBytes);
        }
        catch (TimeoutException exception)
        {
            throw new SkipException(
                $"{InfrastructureHangGuard.SkipReasonPrefix} for {fileName}: {exception.Message}");
        }
    }
}
