using System.Text.Json;

namespace StrataLint.Cli;

internal sealed class AdmissionCheckTiming(TimeProvider timeProvider, bool enabled = true)
{
    internal static AdmissionCheckTiming Disabled { get; } = new(TimeProvider.System, enabled: false);

    // Only phases that take long enough to matter for diagnosis are written.
    internal static TimeSpan ReportingThreshold { get; } = TimeSpan.FromSeconds(1);

    internal T Measure<T>(
        string stage,
        Func<T> action,
        Func<T, bool>? failed = null)
    {
        ArgumentException.ThrowIfNullOrEmpty(stage);
        ArgumentNullException.ThrowIfNull(action);
        var started = enabled ? TryGetTimestamp() : null;
        try
        {
            var result = action();
            Write(stage, failed?.Invoke(result) is true ? "failed" : "passed", started);
            return result;
        }
        catch
        {
            Write(stage, "failed", started);
            throw;
        }
    }

    internal AdmissionCheckTimingAccumulator CreateAccumulator(string stage)
    {
        ArgumentException.ThrowIfNullOrEmpty(stage);
        return new AdmissionCheckTimingAccumulator(this, stage);
    }

    internal long? Start() => enabled ? TryGetTimestamp() : null;

    internal void Accumulate(long? started, ref TimeSpan elapsed)
    {
        if (!enabled || started is null)
        {
            return;
        }

        try
        {
            var duration = timeProvider.GetElapsedTime(started.Value);
            if (duration > TimeSpan.Zero)
            {
                elapsed += duration;
            }
        }
        catch
        {
            // Telemetry cannot change the admission decision when the clock is unavailable.
        }
    }

    internal void Write(string stage, string status, TimeSpan elapsed)
    {
        if (!enabled)
        {
            return;
        }

        try
        {
            WriteEvent(stage, status, Math.Max(0, elapsed.TotalSeconds));
        }
        catch
        {
            // The check result remains the fail-closed signal if timing output is unavailable.
        }
    }

    private long? TryGetTimestamp()
    {
        try
        {
            return timeProvider.GetTimestamp();
        }
        catch
        {
            // Telemetry cannot change the admission decision when the clock is unavailable.
            return null;
        }
    }

    private void Write(string stage, string status, long? started)
    {
        if (!enabled)
        {
            return;
        }

        try
        {
            var elapsedSeconds = started is null
                ? 0
                : Math.Max(0, timeProvider.GetElapsedTime(started.Value).TotalSeconds);
            WriteEvent(stage, status, elapsedSeconds);
        }
        catch
        {
            // The check result remains the fail-closed signal if timing output is unavailable.
        }
    }

    private static void WriteEvent(string stage, string status, double elapsedSeconds)
    {
        if (elapsedSeconds < ReportingThreshold.TotalSeconds)
        {
            return;
        }

        Console.Error.WriteLine(JsonSerializer.Serialize(new
        {
            @event = "gate_stage_timing",
            // A phase outcome is timing data; the admission result owns diagnostics.
            level = "information",
            scope = "admission-check",
            stage,
            status,
            elapsed_seconds = elapsedSeconds,
        }));
    }
}

internal sealed class AdmissionCheckTimingAccumulator(
    AdmissionCheckTiming timing,
    string stage)
{
    private TimeSpan elapsed;
    private bool completed;

    internal T Measure<T>(Func<T> action)
    {
        ArgumentNullException.ThrowIfNull(action);
        var started = timing.Start();
        var failed = false;
        try
        {
            return action();
        }
        catch
        {
            failed = true;
            throw;
        }
        finally
        {
            timing.Accumulate(started, ref elapsed);
            if (failed)
            {
                Complete("failed");
            }
        }
    }

    internal void CompletePassed() => Complete("passed");

    private void Complete(string status)
    {
        if (completed)
        {
            return;
        }

        completed = true;
        timing.Write(stage, status, elapsed);
    }
}
