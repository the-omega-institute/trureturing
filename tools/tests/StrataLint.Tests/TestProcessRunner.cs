global using FactAttribute = Xunit.SkippableFactAttribute;
global using TheoryAttribute = Xunit.SkippableTheoryAttribute;

using StrataLint.Engine;
using System.Runtime.CompilerServices;
using Xunit;

[assembly: InternalsVisibleTo("StrataLint.ArchitectureTests")]

namespace StrataLint.Tests;

internal static class TestProcessRunner
{
    internal static ProcessOutput Run(
        string fileName,
        IEnumerable<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        int maximumOutputBytes,
        ReadOnlyMemory<byte> standardInput = default) =>
        Classify(
            () => BoundedProcessRunner.Run(
                fileName,
                arguments,
                workingDirectory,
                timeout,
                maximumOutputBytes,
                standardInput),
            fileName);

    internal static ProcessOutput Classify(Func<ProcessOutput> run, string command)
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
