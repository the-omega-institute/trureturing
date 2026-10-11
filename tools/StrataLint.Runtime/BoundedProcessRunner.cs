using System.Diagnostics;

namespace StrataLint.Runtime;

internal sealed record ProcessOutput(int ExitCode, byte[] StandardOutput, byte[] StandardError);

internal sealed record StreamedProcessOutput<T>(int ExitCode, T StandardOutput, byte[] StandardError);

internal static class BoundedProcessRunner
{
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
        IReadOnlyDictionary<string, string>? environment = null,
        Stream? standardOutput = null,
        Stream? standardError = null,
        CancellationToken cancellationToken = default,
        Action<Process>? interruptBeforeKill = null)
    {
        var result = RunStreaming(fileName, arguments, workingDirectory, timeout, maximumOutputBytes,
            (stream, cancellation) => ReadLimitedAsync(stream, maximumOutputBytes, cancellation, standardOutput),
            standardInput, environment, standardError, cancellationToken, interruptBeforeKill);
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
        IReadOnlyDictionary<string, string>? environment = null,
        Stream? standardError = null,
        CancellationToken cancellationToken = default,
        Action<Process>? interruptBeforeKill = null)
    {
        cancellationToken.ThrowIfCancellationRequested();
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
        if (!(StartProcess.Value?.Invoke(process) ?? process.Start()))
        {
            throw new InvalidOperationException($"could not start {fileName}");
        }

        using var cancellation = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
        cancellation.CancelAfter(timeout);
        using var drain = new CancellationTokenSource();
        var ioCancellation = interruptBeforeKill is null ? cancellation.Token : drain.Token;
        Task? stdout = null;
        Task? stderr = null;
        Task? stdin = null;
        Exception? interruptionFailure = null;
        try
        {
            var output = readStandardOutput(
                process.StandardOutput.BaseStream,
                ioCancellation);
            stdout = output;
            var errors = ReadLimitedAsync(
                process.StandardError.BaseStream,
                maximumErrorBytes,
                ioCancellation, standardError);
            stderr = errors;
            stdin = standardInput.IsEmpty
                ? Task.CompletedTask
                : WriteInputAsync(
                    process.StandardInput.BaseStream,
                    standardInput,
                    ioCancellation);
            // A failed reader no longer drains its pipe. Observe its failure
            // while the child is running, before a blocked writer can turn an
            // output/parse error into a misleading process timeout.
            var pending = new List<Task>
            {
                stdout, stderr, process.WaitForExitAsync(cancellation.Token),
            };
            while (pending.Count != 0)
            {
                var completed = Task.WhenAny(pending).WaitAsync(cancellation.Token).GetAwaiter().GetResult();
                completed.GetAwaiter().GetResult();
                pending.Remove(completed);
            }
            try
            {
                stdin.GetAwaiter().GetResult();
            }
            catch (IOException) when (process.HasExited)
            {
                // The child owns whether it consumes stdin; preserve its completed verdict.
            }
            return new StreamedProcessOutput<T>(
                process.ExitCode,
                output.GetAwaiter().GetResult(),
                errors.GetAwaiter().GetResult());
        }
        catch (OperationCanceledException exception)
        {
            InterruptAndKill();
            if (cancellationToken.IsCancellationRequested) throw;
            var settlement = interruptionFailure is null ? string.Empty
                : $"; native settlement unresolved: {interruptionFailure.Message}";
            throw new TimeoutException($"{fileName} timed out after {timeout.TotalSeconds:0} seconds{settlement}", exception);
        }
        catch
        {
            InterruptAndKill();
            throw;
        }
        finally
        {
            // Destinations cannot outlive their consumer. In particular, the
            // fixture's settlement output must be drained before its sinks close.
            if (interruptBeforeKill is not null) drain.CancelAfter(TimeSpan.FromSeconds(5));
            else drain.Cancel();
            foreach (var task in new[] { stdout, stderr, stdin })
            {
                try { task?.GetAwaiter().GetResult(); }
                catch (Exception) { /* Preserve the original process/reader failure. */ }
            }
        }

        void InterruptAndKill()
        {
            try
            {
                if (!process.HasExited) interruptBeforeKill?.Invoke(process);
            }
            catch (Exception exception) { interruptionFailure = exception; }
            finally { TryKill(process); }
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
        CancellationToken cancellationToken,
        Stream? destination = null)
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
            if (destination is not null)
            {
                await destination.WriteAsync(buffer.AsMemory(0, count), cancellationToken).ConfigureAwait(false);
                await destination.FlushAsync(cancellationToken).ConfigureAwait(false);
            }
        }
    }

    private static void TryKill(Process process)
    {
        try
        {
            if (!process.HasExited) process.Kill(entireProcessTree: true);
            process.WaitForExit();
        }
        catch (InvalidOperationException)
        {
            // The process exited between HasExited and Kill.
        }
    }
}
