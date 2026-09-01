using System.Diagnostics;

namespace StrataLint.Engine;

internal sealed record ProcessOutput(int ExitCode, byte[] StandardOutput, byte[] StandardError);

internal static class BoundedProcessRunner
{
    internal static readonly TimeSpan HangDetectionBudget = TimeSpan.FromMinutes(5);

    internal static ProcessOutput Run(
        string fileName,
        IEnumerable<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        int maximumOutputBytes,
        ReadOnlyMemory<byte> standardInput = default)
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
        foreach (var argument in arguments)
        {
            startInfo.ArgumentList.Add(argument);
        }

        using var process = new Process { StartInfo = startInfo };
        if (!process.Start())
        {
            throw new InvalidOperationException($"could not start {fileName}");
        }

        using var cancellation = new CancellationTokenSource(timeout);
        try
        {
            var stdout = ReadLimitedAsync(
                process.StandardOutput.BaseStream,
                maximumOutputBytes,
                cancellation.Token);
            var stderr = ReadLimitedAsync(
                process.StandardError.BaseStream,
                maximumOutputBytes,
                cancellation.Token);
            var stdin = standardInput.IsEmpty
                ? Task.CompletedTask
                : WriteInputAsync(
                    process.StandardInput.BaseStream,
                    standardInput,
                    cancellation.Token);
            process.WaitForExitAsync(cancellation.Token).GetAwaiter().GetResult();
            try
            {
                stdin.GetAwaiter().GetResult();
            }
            catch (IOException) when (process.HasExited)
            {
                // The child owns whether it consumes stdin; preserve its completed verdict.
            }
            return new ProcessOutput(
                process.ExitCode,
                stdout.GetAwaiter().GetResult(),
                stderr.GetAwaiter().GetResult());
        }
        catch (OperationCanceledException exception)
        {
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
