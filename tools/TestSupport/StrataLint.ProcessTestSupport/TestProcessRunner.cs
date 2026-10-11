using StrataLint.Runtime;
using System.Diagnostics;
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
        Stream? standardError = null,
        Action<Process>? interruptBeforeKill = null) =>
        Classify(
            () => BoundedProcessRunner.Run(
                fileName,
                arguments,
                workingDirectory,
                timeout,
                maximumOutputBytes,
                standardInput,
                standardOutput: standardOutput,
                standardError: standardError,
                interruptBeforeKill: interruptBeforeKill),
            fileName);

    internal static void InterruptPythonFixture(Process process)
    {
        // The fixture owns its new native sessions. Signal only its interpreter,
        // so it can settle those sessions and publish evidence before hard kill.
        var signal = BoundedProcessRunner.Run("/bin/kill", ["-TERM", process.Id.ToString(
                System.Globalization.CultureInfo.InvariantCulture)], process.StartInfo.WorkingDirectory,
            TimeSpan.FromSeconds(5), 4096);
        if (signal.ExitCode != 0 && !process.HasExited)
            throw new InvalidOperationException("fixture interruption could not be delivered");
        // This joins settlement; it does not extend the interrupted test body.
        if (!process.WaitForExit(20000))
            throw new InvalidOperationException("fixture native settlement remains unresolved");
    }

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
