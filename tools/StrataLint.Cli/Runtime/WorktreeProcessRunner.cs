using StrataLint.Engine;

namespace StrataLint.Cli;

internal interface IWorktreeProcessRunner
{
    ProcessOutput Run(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout);
}

internal sealed class ProductionWorktreeProcessRunner : IWorktreeProcessRunner
{
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
