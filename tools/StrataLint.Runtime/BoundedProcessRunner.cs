using System.Diagnostics;

namespace StrataLint.Runtime;

internal sealed record ProcessOutput(int ExitCode, byte[] StandardOutput, byte[] StandardError);

internal sealed record StreamedProcessOutput<T>(int ExitCode, T StandardOutput, byte[] StandardError);

internal static class BoundedProcessRunner
{
    internal static readonly TimeSpan HangDetectionBudget = TimeSpan.FromMinutes(5);
    private static readonly object StartFailureKey = new();

    internal static bool FailedBeforeStart(Exception exception) => exception.Data[StartFailureKey] is true;

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
        var observations = new CompletionObservations();
        var result = RunStreaming(observations, fileName, arguments, workingDirectory, timeout, maximumOutputBytes,
            (stream, cancellation) => ReadLimitedAsync(stream, maximumOutputBytes, cancellation, standardOutput,
                observations, "stdout"),
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
        => RunStreaming(new CompletionObservations(), fileName, arguments, workingDirectory, timeout,
            maximumErrorBytes, readStandardOutput, standardInput, environment, standardError,
            cancellationToken, interruptBeforeKill);

    private static StreamedProcessOutput<T> RunStreaming<T>(
        CompletionObservations observations,
        string fileName,
        IEnumerable<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        int maximumErrorBytes,
        Func<Stream, CancellationToken, Task<T>> readStandardOutput,
        ReadOnlyMemory<byte> standardInput,
        IReadOnlyDictionary<string, string>? environment,
        Stream? standardError,
        CancellationToken cancellationToken,
        Action<Process>? interruptBeforeKill)
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
        try
        {
            if (!(StartProcess.Value?.Invoke(process) ?? process.Start()))
                throw new InvalidOperationException($"could not start {fileName}");
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            exception.Data[StartFailureKey] = true;
            throw;
        }

        using var cancellation = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
        cancellation.CancelAfter(timeout);
        observations.Cancellation = cancellation.Token;
        using var cancellationObservation = cancellation.Token.Register(
            () => observations.Record("cancellation.callback", "invoked"));
        using var drain = new CancellationTokenSource();
        // Execution cancellation settles the child first. Its complete pipe
        // observations remain readable until EOF or the bounded drain expires.
        var ioCancellation = drain.Token;
        Task? stdout = null;
        Task? stderr = null;
        Task? stdin = null;
        Task? exitWait = null;
        Task? stdoutObservation = null;
        Task? stderrObservation = null;
        Task? exitObservation = null;
        var operation = "stdout.start";
        Exception? interruptionFailure = null;
        try
        {
            var output = readStandardOutput(
                process.StandardOutput.BaseStream,
                ioCancellation);
            stdout = output;
            stdoutObservation = observations.ObserveCompletion(output, "stdout.complete");
            operation = "stderr.start";
            var errors = ReadLimitedAsync(
                process.StandardError.BaseStream,
                maximumErrorBytes,
                ioCancellation, standardError, observations, "stderr");
            stderr = errors;
            stderrObservation = observations.ObserveCompletion(errors, "stderr.complete");
            operation = "stdin.start";
            stdin = standardInput.IsEmpty
                ? Task.CompletedTask
                : WriteInputAsync(
                    process.StandardInput.BaseStream,
                    standardInput,
                    ioCancellation, observations);
            if (standardInput.IsEmpty) observations.Record("stdin", "not-redirected");
            operation = "exit-wait.start";
            exitWait = process.WaitForExitAsync(cancellation.Token);
            exitObservation = observations.ObserveCompletion(exitWait, "exit-wait.complete");
            // A failed reader no longer drains its pipe. Observe its failure
            // while the child is running, before a blocked writer can turn an
            // output/parse error into a misleading process timeout.
            var pending = new List<Task>
            {
                stdout, stderr, exitWait,
            };
            while (pending.Count != 0)
            {
                operation = "completion-arbitration";
                var completed = Task.WhenAny(pending).WaitAsync(cancellation.Token).GetAwaiter().GetResult();
                operation = completed == stdout ? "stdout.result"
                    : completed == stderr ? "stderr.result" : "exit-wait.result";
                completed.GetAwaiter().GetResult();
                pending.Remove(completed);
            }
            try
            {
                operation = "stdin.result";
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
            // Freeze the evidence before interruption, kill and joining can change it.
            var completion = observations.Snapshot(process, stdout, stderr, stdin, exitWait,
                operation, exception, cancellationToken, ioCancellation);
            InterruptAndKill();
            if (cancellationToken.IsCancellationRequested) throw;
            var settlement = interruptionFailure is null ? string.Empty
                : $"; native settlement unresolved: {interruptionFailure.Message}";
            throw new TimeoutException($"{fileName} timed out after {timeout.TotalSeconds:0} seconds{settlement}; {completion}", exception);
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
            drain.CancelAfter(TimeSpan.FromSeconds(5));
            foreach (var task in new[] { stdout, stderr, stdin, stdoutObservation, stderrObservation, exitObservation })
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
        CancellationToken cancellationToken,
        CompletionObservations observations)
    {
        var operation = "stdin.write";
        try
        {
            await stream.WriteAsync(bytes, cancellationToken).ConfigureAwait(false);
            observations.Record(operation, $"completed(bytes={bytes.Length})");
            operation = "stdin.flush";
            await stream.FlushAsync(cancellationToken).ConfigureAwait(false);
            observations.Record(operation, "completed");
        }
        catch (Exception exception)
        {
            observations.Record(operation, $"threw({exception.GetType().FullName})");
            throw;
        }
        finally
        {
            try
            {
                stream.Close();
                observations.Record("stdin.close", "completed");
            }
            catch (Exception exception)
            {
                observations.Record("stdin.close", $"threw({exception.GetType().FullName})");
                throw;
            }
        }
    }

    private static async Task<byte[]> ReadLimitedAsync(
        Stream stream,
        int maximumBytes,
        CancellationToken cancellationToken,
        Stream? destination,
        CompletionObservations observations,
        string channel)
    {
        var byteStage = $"{channel}.bytes";
        observations.Record(byteStage, 0);
        using var memory = new MemoryStream();
        var buffer = new byte[8192];
        while (true)
        {
            var count = await stream.ReadAsync(buffer, cancellationToken).ConfigureAwait(false);
            if (count == 0)
            {
                observations.Record($"{channel}.eof", "observed");
                return memory.ToArray();
            }
            observations.Record(byteStage, memory.Length + count);
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

    // Entries order observations, not the underlying OS events. A false cancellation
    // sample proves the recorded milestone preceded the request; true cannot date it.
    // The cancellation callback dates its own execution, not the deadline instant.
    // Custom stdout readers expose completion only, so their byte count/EOF stay unknown.
    // HasExited is probed only before timeout cleanup; it cannot date the original exit.
    internal sealed class CompletionObservations
    {
        private readonly object gate = new();
        private readonly Dictionary<string, Observation> entries = new(StringComparer.Ordinal);
        private readonly Dictionary<string, Observation> beforeCancellation = new(StringComparer.Ordinal);
        private readonly record struct Observation(object Value, int Sequence, bool CancellationRequested)
        {
            public override string ToString() =>
                $"{Convert.ToString(Value, System.Globalization.CultureInfo.InvariantCulture)}#{Sequence}"
                + $"(cancel-requested={CancellationRequested.ToString().ToLowerInvariant()})";
        }
        private int sequence;
        internal CancellationToken Cancellation { private get; set; }

        internal void Record(string name, object value)
        {
            lock (gate)
            {
                var canceled = Cancellation.IsCancellationRequested;
                var entry = new Observation(value, ++sequence, canceled);
                entries[name] = entry;
                // Keep a useful pre-request lower bound even if a later read/probe wins the snapshot.
                if (!canceled) beforeCancellation[name] = entry;
            }
        }

        internal async Task ObserveCompletion(Task task, string name)
        {
            try
            {
                await task.ConfigureAwait(false);
                Record(name, "completed");
            }
            catch (Exception exception)
            {
                Record(name, $"threw({exception.GetType().FullName})");
                throw;
            }
        }

        internal void ObserveExit(Process process, string name)
        {
            lock (gate)
            {
                var before = Cancellation.IsCancellationRequested;
                string value;
                try { value = process.HasExited.ToString().ToLowerInvariant(); }
                catch (Exception exception)
                {
                    value = $"unknown(threw {exception.GetType().FullName}: {exception.Message})";
                }
                // Both samples must be false to locate this probe before cancellation.
                Record(name, $"{value}(cancel-before={before.ToString().ToLowerInvariant()})");
            }
        }

        internal string Snapshot(Process process, Task? stdout, Task? stderr, Task? stdin, Task? exitWait,
            string operation, OperationCanceledException exception, CancellationToken caller,
            CancellationToken ioCancellation)
        {
            lock (gate)
            {
                ObserveExit(process, "has-exited.before-cleanup");
                var origin = !exception.CancellationToken.CanBeCanceled ? "none"
                    : exception.CancellationToken == Cancellation ? "shared-linked"
                    : exception.CancellationToken == ioCancellation ? "io"
                    : exception.CancellationToken == caller ? "caller" : "other-or-none";
                var stages = new[] { "stdin", "stdin.write", "stdin.flush", "stdin.close", "stdout.bytes",
                    "stdout.eof", "stdout.complete", "stderr.bytes", "stderr.eof", "stderr.complete",
                    "exit-wait.complete", "cancellation.callback", "has-exited.before-cleanup" };
                var bounds = new[] { "stdout.bytes", "stderr.bytes" };
                return "completion observations [record-order-only; unknown=not-observed; snapshot=non-atomic-before-cleanup; "
                    + $"exception-site={operation}; exception-type={exception.GetType().FullName}; exception-message={exception.Message}; token={origin}; "
                    + $"caller-cancel-requested={caller.IsCancellationRequested.ToString().ToLowerInvariant()}; "
                    + string.Join("; ", stages.Select(name => $"{name}={Read(entries, name)}")
                        .Concat(bounds.Select(name => $"{name}.before-cancel={Read(beforeCancellation, name)}")))
                    + $"; task-status-sampled-before-cleanup: stdout={Status(stdout)}, stderr={Status(stderr)}, "
                    + $"stdin={Status(stdin)}, exit-wait={Status(exitWait)}]";
            }
        }

        private static string Read(Dictionary<string, Observation> source, string name) =>
            source.TryGetValue(name, out var entry) ? entry.ToString() : "unknown";

        private static string Status(Task? task) => task?.Status.ToString() ?? "not-created";
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
