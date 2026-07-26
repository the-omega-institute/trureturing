using System.Collections.Concurrent;
using System.Diagnostics;
using System.Text;
using StrataLint.Engine;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace StrataLint.Tests;

public sealed class ReportFactAttribute : FactAttribute;

public sealed class ReportTheoryAttribute : TheoryAttribute;

[CollectionDefinition(Name, DisableParallelization = true)]
public sealed class ReportSupervisorScriptCollection
{
    public const string Name = "report-supervisor-script-tests";
}

internal sealed class ReportSupervisorTestWatchdog : IDisposable
{
    private const int TailCharacterLimit = 8_192;
    private const string TimeoutEnvironment = "STRATALINT_REPORT_TEST_TIMEOUT_SECONDS";
    private static readonly AsyncLocal<ReportSupervisorTestWatchdog?> ambient = new();
    private readonly ConcurrentDictionary<int, Process> processes = new();
    private readonly object diagnosticsLock = new();
    private readonly ITestOutputHelper output;
    private readonly Timer timer;
    private readonly string timeoutDescription;
    private string stdout = string.Empty;
    private string stderr = string.Empty;
    private int timedOut;

    internal ReportSupervisorTestWatchdog(ITestOutputHelper output)
        : this(output, TimeSpan.FromSeconds(ConfiguredTimeoutSeconds))
    {
    }

    internal ReportSupervisorTestWatchdog(ITestOutputHelper output, TimeSpan timeout)
    {
        this.output = output;
        timeoutDescription = timeout.TotalSeconds >= 1
            ? $"{timeout.TotalSeconds:0}s"
            : $"{timeout.TotalMilliseconds:0}ms";
        ambient.Value = this;
        timer = new Timer(
            static state => ((ReportSupervisorTestWatchdog)state!).OnTimeout(),
            this,
            timeout,
            Timeout.InfiniteTimeSpan);
    }

    internal static ReportSupervisorTestWatchdog? Current => ambient.Value;

    internal static int ConfiguredTimeoutSeconds => ParseTimeoutSeconds(
        Environment.GetEnvironmentVariable(TimeoutEnvironment));

    internal static int ParseTimeoutSeconds(string? value) =>
        int.TryParse(value, out var seconds) && seconds is >= 1 and <= 3_600
            ? seconds
            : 90;

    internal void RecordStandardOutput(string text)
    {
        lock (diagnosticsLock) stdout = AppendTail(stdout, text);
    }

    internal void RecordStandardError(string text)
    {
        lock (diagnosticsLock) stderr = AppendTail(stderr, text);
    }

    internal void Track(Process process, bool captureOutput = true)
    {
        processes[process.Id] = process;
        process.EnableRaisingEvents = true;
        process.Exited += (_, _) => processes.TryRemove(process.Id, out _);
        if (!captureOutput) return;
        process.OutputDataReceived += (_, eventArgs) => AppendProcessLine(ref stdout, eventArgs.Data);
        process.ErrorDataReceived += (_, eventArgs) => AppendProcessLine(ref stderr, eventArgs.Data);
        process.BeginOutputReadLine();
        process.BeginErrorReadLine();
    }

    internal static string FormatDiagnostics(string testName, string stdout, string stderr) =>
        $"report test watchdog timed out: {testName}\n"
        + $"--- stdout tail ---\n{Tail(stdout)}\n"
        + $"--- stderr tail ---\n{Tail(stderr)}";

    public void Dispose()
    {
        timer.DisposeAsync().AsTask().GetAwaiter().GetResult();
        if (ReferenceEquals(ambient.Value, this)) ambient.Value = null;
        if (Volatile.Read(ref timedOut) != 0)
        {
            throw new XunitException(SnapshotDiagnostics());
        }
    }

    private void OnTimeout()
    {
        if (Interlocked.Exchange(ref timedOut, 1) != 0) return;
        var diagnostics = SnapshotDiagnostics();
        try
        {
            output.WriteLine(diagnostics);
        }
        catch (Exception)
        {
            Console.Error.WriteLine(diagnostics);
        }

        foreach (var process in processes.Values)
        {
            TryKill(process);
        }
    }

    private string SnapshotDiagnostics()
    {
        lock (diagnosticsLock)
        {
            return FormatDiagnostics(
                $"ReportSupervisorScriptTests ({timeoutDescription})",
                stdout,
                stderr);
        }
    }

    private void AppendProcessLine(ref string destination, string? line)
    {
        if (line is null) return;
        lock (diagnosticsLock)
        {
            destination = AppendTail(destination, line + "\n");
        }
    }

    private static string AppendTail(string existing, string addition) => Tail(existing + addition);

    private static string Tail(string value) => value.Length <= TailCharacterLimit
        ? value
        : value[^TailCharacterLimit..];

    private static void TryKill(Process process)
    {
        try
        {
            if (!process.HasExited) process.Kill(entireProcessTree: true);
        }
        catch (InvalidOperationException)
        {
            // The process exited concurrently with the watchdog.
        }
        catch (System.ComponentModel.Win32Exception)
        {
            // Timeout diagnostics were captured before this best-effort termination.
        }
    }
}

internal static class ReportSupervisorTestProcessRunner
{
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
        foreach (var argument in arguments) startInfo.ArgumentList.Add(argument);

        using var process = new Process { StartInfo = startInfo };
        if (!process.Start()) throw new InvalidOperationException($"could not start {fileName}");
        ReportSupervisorTestWatchdog.Current?.Track(process, captureOutput: false);
        var watchdog = ReportSupervisorTestWatchdog.Current;
        Action<string>? stdoutRecorder = watchdog is null ? null : watchdog.RecordStandardOutput;
        Action<string>? stderrRecorder = watchdog is null ? null : watchdog.RecordStandardError;
        using var cancellation = new CancellationTokenSource(timeout);
        var stdout = ReadLimitedAsync(
            process.StandardOutput.BaseStream,
            maximumOutputBytes,
            stdoutRecorder,
            cancellation.Token);
        var stderr = ReadLimitedAsync(
            process.StandardError.BaseStream,
            maximumOutputBytes,
            stderrRecorder,
            cancellation.Token);
        var stdin = standardInput.IsEmpty
            ? Task.CompletedTask
            : WriteInputAsync(process.StandardInput.BaseStream, standardInput, cancellation.Token);
        ProcessOutput result;
        try
        {
            process.WaitForExitAsync(cancellation.Token).GetAwaiter().GetResult();
            stdin.GetAwaiter().GetResult();
            result = new ProcessOutput(
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
        return result;
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
        Action<string>? record,
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
            record?.Invoke(Encoding.UTF8.GetString(buffer, 0, count));
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
            // The process exited between observation and termination.
        }
    }
}
