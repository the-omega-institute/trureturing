using System.Collections.Concurrent;
using System.Diagnostics;
using Xunit.Sdk;

namespace StrataLint.Tests;

internal sealed class ReportSupervisorTestWatchdog : IDisposable
{
    private const int TailCharacterLimit = 8_192;
    private readonly ConcurrentDictionary<int, Process> processes = new();
    private readonly object diagnosticsLock = new();
    private readonly Timer timer;
    private readonly string timeoutDescription;
    private string stdout = string.Empty;
    private string stderr = string.Empty;
    private int timedOut;
    private int disposed;
    private int timeoutReported;

    internal ReportSupervisorTestWatchdog(TimeSpan timeout)
    {
        timeoutDescription = timeout.TotalSeconds >= 1
            ? $"{timeout.TotalSeconds:0}s"
            : $"{timeout.TotalMilliseconds:0}ms";
        timer = new Timer(
            static state => ((ReportSupervisorTestWatchdog)state!).OnTimeout(),
            this,
            timeout,
            Timeout.InfiniteTimeSpan);
    }

    internal void Track(Process process)
    {
        processes[process.Id] = process;
        process.EnableRaisingEvents = true;
        process.Exited += (_, _) => processes.TryRemove(process.Id, out _);
        process.OutputDataReceived += (_, eventArgs) => AppendLine(ref stdout, eventArgs.Data);
        process.ErrorDataReceived += (_, eventArgs) => AppendLine(ref stderr, eventArgs.Data);
        process.BeginOutputReadLine();
        process.BeginErrorReadLine();
    }

    public void Dispose()
    {
        if (Interlocked.Exchange(ref disposed, 1) == 0)
        {
            timer.DisposeAsync().AsTask().GetAwaiter().GetResult();
            foreach (var process in processes.Values) TryKill(process);
        }
        if (Volatile.Read(ref timedOut) != 0
            && Interlocked.Exchange(ref timeoutReported, 1) == 0)
        {
            throw new XunitException(SnapshotDiagnostics());
        }
    }

    private void OnTimeout()
    {
        if (Interlocked.Exchange(ref timedOut, 1) != 0) return;
        foreach (var process in processes.Values) TryKill(process);
    }

    private string SnapshotDiagnostics()
    {
        lock (diagnosticsLock)
        {
            return $"report supervisor test timed out after {timeoutDescription}\n"
                + $"--- stdout tail ---\n{stdout}\n"
                + $"--- stderr tail ---\n{stderr}";
        }
    }

    private void AppendLine(ref string destination, string? line)
    {
        if (line is null) return;
        lock (diagnosticsLock)
        {
            destination += line + "\n";
            if (destination.Length > TailCharacterLimit)
            {
                destination = destination[^TailCharacterLimit..];
            }
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
            // The process exited concurrently with cleanup.
        }
        catch (System.ComponentModel.Win32Exception)
        {
            // The typed timeout still reports the failed termination attempt.
        }
    }
}
