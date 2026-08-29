using System.Globalization;
using ProcessAlias = System.Diagnostics.Process;

namespace StrataLint.BannedApiCompileFailProof;

internal static class BannedApiViolations
{
    internal static object[] MustNotCompile()
    {
        Thread.Sleep(1); // banned-api-proof
        Thread.Sleep(TimeSpan.Zero); // banned-api-proof
        _ = Task.Delay(1); // banned-api-proof
        _ = Task.Delay(1, CancellationToken.None); // banned-api-proof
        _ = Task.Delay(TimeSpan.Zero); // banned-api-proof
        _ = Task.Delay(TimeSpan.Zero, CancellationToken.None); // banned-api-proof
        _ = Task.Delay(TimeSpan.Zero, TimeProvider.System); // banned-api-proof
        _ = Task.Delay(TimeSpan.Zero, TimeProvider.System, CancellationToken.None); // banned-api-proof
        _ = System.Diagnostics.Stopwatch.StartNew(); // banned-api-proof
        _ = new ProcessAlias(); // banned-api-proof
        _ = new System.Diagnostics.ProcessStartInfo(); // banned-api-proof
        StrataLint.Engine.BoundedProcessRunner.Run(); // banned-api-proof
        StrataLint.Tests.TestProcessRunner.Run(); // banned-api-proof
        return
        [
        DateTime.Now, // banned-api-proof
        DateTime.UtcNow, // banned-api-proof
        DateTimeOffset.Now, // banned-api-proof
        DateTimeOffset.UtcNow, // banned-api-proof
        new Random(), // banned-api-proof
        Environment.TickCount, // banned-api-proof
        Environment.TickCount64, // banned-api-proof
        Guid.NewGuid(), // banned-api-proof
        int.Parse("1"), // banned-api-proof
        1.ToString(), // banned-api-proof
        int.Parse("1", NumberStyles.Integer), // banned-api-proof
        double.TryParse("1".AsSpan(), out _), // banned-api-proof
        Half.Parse("1"), // banned-api-proof
        DateOnly.Parse("2026-07-12"), // banned-api-proof
        TimeOnly.Parse("12:34"), // banned-api-proof
        1.ToString("N0"), // banned-api-proof
        DateOnly.ParseExact("2026-07-12", "yyyy-MM-dd"), // banned-api-proof
        TimeOnly.TryParseExact("12:34".AsSpan(), "HH:mm".AsSpan(), out _), // banned-api-proof
        ];
    }
}
