using System.Diagnostics;

namespace StrataLint.Engine;

internal sealed record ProcessOutput(int ExitCode, byte[] StandardOutput, byte[] StandardError);

internal sealed record StreamedProcessOutput<T>(int ExitCode, T StandardOutput, byte[] StandardError);

internal static class BoundedProcessRunner
{
    internal delegate ProcessOutput ProcessRunner(
        string fileName,
        IEnumerable<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        int maximumOutputBytes,
        ReadOnlyMemory<byte> standardInput = default,
        IReadOnlyDictionary<string, string>? environment = null);

    internal static readonly TimeSpan HangDetectionBudget = TimeSpan.FromMinutes(5);

    // Flow the startup seam into Task.Run without sharing overrides between checks.
    internal static readonly AsyncLocal<Func<Process, bool>?> StartProcess = new();

    internal static ProcessOutput Run(
        string fileName,
        IEnumerable<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        int maximumOutputBytes,
        ReadOnlyMemory<byte> standardInput = default,
        IReadOnlyDictionary<string, string>? environment = null)
    {
        var result = RunStreaming(fileName, arguments, workingDirectory, timeout, maximumOutputBytes,
            (stream, cancellation) => ReadLimitedAsync(stream, maximumOutputBytes, cancellation),
            standardInput, environment);
        return new ProcessOutput(result.ExitCode, result.StandardOutput, result.StandardError);
    }

    internal static StreamedProcessOutput<T> RunStreaming<T>(
        string fileName,
        IEnumerable<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        int maximumErrorBytes,
        Func<Stream, CancellationToken, Task<T>> readStandardOutput,
        ReadOnlyMemory<byte> standardInput = default,
        IReadOnlyDictionary<string, string>? environment = null)
    {
        var startInfo = new ProcessStartInfo
        {
            FileName = fileName,
            WorkingDirectory = workingDirectory,
            UseShellExecute = false,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            RedirectStandardInput = !standardInput.IsEmpty,
            CreateNoWindow = true,
        };
        if (environment is not null)
        {
            startInfo.Environment.Clear();
            foreach (var (name, value) in environment)
            {
                startInfo.Environment.Add(name, value);
            }
        }
        foreach (var argument in arguments)
        {
            startInfo.ArgumentList.Add(argument);
        }

        using var process = new Process { StartInfo = startInfo };
        var probe = DefaultCliStartupProbe.Current.Value;
        probe?.ConfigureGit(startInfo);
        probe?.Mark("process-before-start", new { executable = Path.GetFileName(fileName), arguments = startInfo.ArgumentList.ToArray() });
        if (!(StartProcess.Value?.Invoke(process) ?? process.Start()))
        {
            throw new InvalidOperationException($"could not start {fileName}");
        }
        var startReturned = probe is null ? 0 : TimeProvider.System.GetTimestamp();
        using var cancellation = new CancellationTokenSource(timeout);
        var guardCreated = probe is null ? 0 : TimeProvider.System.GetTimestamp();
        probe?.Mark("process-start-return", new { child_pid = process.Id }, startReturned);
        probe?.Mark("guard-created", new { timeout_seconds = timeout.TotalSeconds, maximum_error_bytes = maximumErrorBytes }, guardCreated);
        try
        {
            probe?.Resources("guard-created");
            probe?.Mark("stream-setup-begin");
            var stdout = readStandardOutput(
                process.StandardOutput.BaseStream,
                cancellation.Token);
            var stderr = ReadLimitedAsync(
                process.StandardError.BaseStream,
                maximumErrorBytes,
                cancellation.Token);
            var stdin = standardInput.IsEmpty
                ? Task.CompletedTask
                : WriteInputAsync(
                    process.StandardInput.BaseStream,
                    standardInput,
                    cancellation.Token);
            probe?.Mark("wait-begin");
            process.WaitForExitAsync(cancellation.Token).GetAwaiter().GetResult();
            probe?.ProcessState("observed-exit", process);
            try
            {
                stdin.GetAwaiter().GetResult();
            }
            catch (IOException) when (process.HasExited)
            {
                // The child owns whether it consumes stdin; preserve its completed verdict.
            }
            probe?.Mark("stream-drain-begin");
            var result = new StreamedProcessOutput<T>(
                process.ExitCode,
                stdout.GetAwaiter().GetResult(),
                stderr.GetAwaiter().GetResult());
            probe?.Mark("stream-drain-end");
            probe?.Resources("observed-exit");
            return result;
        }
        catch (OperationCanceledException exception)
        {
            // Capture liveness before TryKill; never query child CPU after exit.
            probe?.ProcessState("timeout-before-kill", process);
            probe?.Resources("timeout-before-kill");
            TryKill(process);
            throw new TimeoutException($"{fileName} timed out after {timeout.TotalSeconds:0} seconds", exception);
        }
        catch
        {
            TryKill(process);
            throw;
        }
    }

    private static async Task WriteInputAsync(
        Stream stream,
        ReadOnlyMemory<byte> bytes,
        CancellationToken cancellationToken)
    {
        try
        {
            await stream.WriteAsync(bytes, cancellationToken).ConfigureAwait(false);
            await stream.FlushAsync(cancellationToken).ConfigureAwait(false);
        }
        finally
        {
            stream.Close();
        }
    }

    private static async Task<byte[]> ReadLimitedAsync(
        Stream stream,
        int maximumBytes,
        CancellationToken cancellationToken)
    {
        using var memory = new MemoryStream();
        var buffer = new byte[8192];
        while (true)
        {
            var count = await stream.ReadAsync(buffer, cancellationToken).ConfigureAwait(false);
            if (count == 0) return memory.ToArray();
            if (memory.Length + count > maximumBytes)
            {
                throw new InvalidOperationException($"process output exceeded {maximumBytes} bytes");
            }

            await memory.WriteAsync(buffer.AsMemory(0, count), cancellationToken).ConfigureAwait(false);
        }
    }

    private static void TryKill(Process process)
    {
        try
        {
            if (!process.HasExited) process.Kill(entireProcessTree: true);
        }
        catch (InvalidOperationException)
        {
            // The process exited between HasExited and Kill.
        }
    }
}
