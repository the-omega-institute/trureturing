using StrataLint.Runtime;
using StrataLint.Engine;
using System.Diagnostics;
using System.Globalization;
using System.Collections;

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

internal sealed class ProductionWorktreeProcessRunner(CancellationToken cancellationToken = default,
    LeanCacheCommandObservation? observation = null,
    IReadOnlyDictionary<string, string>? environment = null) : IWorktreeProcessRunner
{
    internal ProductionWorktreeProcessRunner WithEnvironment(IReadOnlyDictionary<string, string> variables)
    {
        ArgumentNullException.ThrowIfNull(variables);
        // BoundedProcessRunner treats a non-null environment as a complete
        // environment.  Keep the normal process environment and overlay only
        // the routing variables selected by the cache wrapper.
        var merged = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
        foreach (DictionaryEntry entry in Environment.GetEnvironmentVariables())
            if (entry.Key is string name && entry.Value is string value)
                merged[name] = value;
        if (environment is not null)
            foreach (var (name, value) in environment)
                merged[name] = value;
        foreach (var (name, value) in variables)
            merged[name] = value;
        return new(cancellationToken, observation, merged);
    }

    public ProcessOutput Run(
        string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan timeout,
        Stream? standardOutput, Stream? standardError)
    {
        observation?.Boundary("cache-child", "start", fileName, arguments, workingDirectory);
        try
        {
            var result = BoundedProcessRunner.Run(fileName, arguments, workingDirectory, timeout,
                64 * 1024 * 1024, environment: environment,
                standardOutput: observation?.Output(standardOutput) ?? standardOutput,
                standardError: observation?.Error(standardError) ?? standardError, cancellationToken: cancellationToken,
                interruptBeforeKill: fileName == "/bin/bash" && arguments.Count > 1
                    && arguments[0] == LeanArchiveFetch.ScriptPath(workingDirectory) && arguments[1] == "fetch"
                    ? InterruptArchive : null);
            observation?.Boundary("cache-child", "finish", fileName, arguments, workingDirectory, result.ExitCode);
            return result;
        }
        catch (Exception error)
        {
            observation?.Boundary("cache-child", "finish", fileName, arguments, workingDirectory,
                error: error.GetType().FullName + ": " + error.Message);
            throw;
        }
    }

    public StreamedProcessOutput<T> RunStreaming<T>(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        Func<Stream, CancellationToken, Task<T>> readStandardOutput) =>
        BoundedProcessRunner.RunStreaming(fileName, arguments, workingDirectory, timeout,
            64 * 1024 * 1024, readStandardOutput, environment: environment, cancellationToken: cancellationToken);

    public ProcessOutput Run(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout) =>
        Run(fileName, arguments, workingDirectory, timeout, null, null);

    private static void InterruptArchive(Process process)
    {
        if (OperatingSystem.IsWindows()) return;
        // The archive shell execs Python. Let its existing BaseException rollback
        // and owned transport settlement complete before the runner's hard stop.
        _ = BoundedProcessRunner.Run("/bin/kill", ["-TERM", process.Id.ToString(CultureInfo.InvariantCulture)],
            process.StartInfo.WorkingDirectory, TimeSpan.FromSeconds(5), 4096);
        if (!process.WaitForExit(5000))
            throw new InvalidOperationException("archive interruption did not settle before the hard stop");
    }
}
