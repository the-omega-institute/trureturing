using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class CurrentDeadlineContractTests
{
    [Theory]
    [InlineData(null, 7200, 0)]
    [InlineData(null, 21599, 0)]
    [InlineData(null, 21600, 124)]
    [InlineData("2000000100", 99, 0)]
    [InlineData("2000000100", 100, 124)]
    public void ReportHonorsNormalLeanEnvelopeAndExplicitOuterDeadline(string? deadline, int advanceSeconds, int rawExit)
    {
        WithDeadline(deadline, () =>
        {
            using var fixture = new CurrentExecutionContractTests.CandidateFixture();
            CommonStageContractTests.PrepareCurrent(fixture);
            TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, "build/producer.sh"), "printf 'producer-out'\nprintf 'producer-error' >&2\n");
            var clock = new ManualClock();
            using var output = new StringWriter();
            Assert.Equal(2, new CommonStages(fixture.Root, output,
                processExited: _ => clock.Advance(advanceSeconds), timeProvider: clock).Run("current", null));
            using var summary = JsonDocument.Parse(TemporaryFileSystem.File.ReadAllText(
                Path.Combine(fixture.Root, "build/ci/current-result.json")));
            var step = Assert.Single(summary.RootElement.GetProperty("steps").EnumerateArray());
            Assert.Equal(rawExit, step.GetProperty("raw_exit").GetInt32());
            Assert.Equal(deadline is null ? 21600 : 100, clock.DueTime!.Value.TotalSeconds);
            Assert.Equal(rawExit == 0 ? "executed" : "failed", step.GetProperty("status").GetString());
            var observation = CommonStageContractTests.ProcessObservation(output);
            Assert.Equal(0, observation.GetProperty("child_exit").GetProperty("elapsed_ms").GetDouble());
            Assert.Equal(advanceSeconds * 1000, observation.GetProperty("elapsed_ms").GetDouble());
            Assert.Equal(rawExit == 0 ? "completed" : "cancelled", observation.GetProperty("outcome").GetString());
            Assert.Equal(rawExit != 0, observation.GetProperty("timeout_cancelled").GetBoolean());
            Assert.False(observation.GetProperty("deadline_cancelled").GetBoolean());
            if (rawExit != 0)
            {
                Assert.Equal("output-drain", observation.GetProperty("cancelled_phase").GetString());
                Assert.Equal(advanceSeconds * 1000, observation.GetProperty("cancelled_elapsed_ms").GetDouble());
            }
            Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
            Assert.Throws<FileNotFoundException>(() => CommonExecutionEvidence.ValidateCurrent(fixture.Root));
        });
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void InjectedCancellationOwnsDeadlineWithoutAmbientClock(bool cancel)
    {
        WithDeadline("invalid-ambient-deadline", () =>
        {
            using var fixture = new CurrentExecutionContractTests.CandidateFixture();
            CommonStageContractTests.PrepareCurrent(fixture);
            TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, "build/producer.sh"), "printf 'producer-out'\n");
            using var cancellation = new CancellationTokenSource();
            var clock = new ManualClock();
            using var output = new StringWriter();
            Assert.Equal(2, new CommonStages(fixture.Root, output, cancellation.Token,
                _ => { if (cancel) cancellation.Cancel(); }, clock).Run("current", null));
            using var summary = JsonDocument.Parse(TemporaryFileSystem.File.ReadAllText(
                Path.Combine(fixture.Root, "build/ci/current-result.json")));
            Assert.Equal(cancel ? 124 : 0, Assert.Single(summary.RootElement.GetProperty("steps").EnumerateArray())
                .GetProperty("raw_exit").GetInt32());
            Assert.Equal(Timeout.InfiniteTimeSpan, clock.DueTime);
        });
    }

    private static void WithDeadline(string? value, Action body)
    {
        var original = Environment.GetEnvironmentVariable("PREFLIGHT_DEADLINE_AT");
        try { Environment.SetEnvironmentVariable("PREFLIGHT_DEADLINE_AT", value); body(); }
        finally { Environment.SetEnvironmentVariable("PREFLIGHT_DEADLINE_AT", original); }
    }

    internal sealed class ManualClock : TimeProvider
    {
        private DateTimeOffset now = DateTimeOffset.FromUnixTimeSeconds(2000000000);
        private long timestamp;
        private ManualTimer? timer;
        internal TimeSpan? DueTime { get; private set; }
        public override DateTimeOffset GetUtcNow() => now;
        public override long TimestampFrequency => 1;
        public override long GetTimestamp() => Interlocked.Read(ref timestamp);
        public override ITimer CreateTimer(TimerCallback callback, object? state, TimeSpan dueTime, TimeSpan period)
        {
            DueTime = dueTime;
            return timer = new ManualTimer(callback, state, now + dueTime);
        }
        internal void Advance(int seconds)
        {
            now += TimeSpan.FromSeconds(seconds);
            Interlocked.Add(ref timestamp, seconds);
            if (DueTime != Timeout.InfiniteTimeSpan && timer is { Disposed: false } && now >= timer.Deadline) timer.Fire();
        }
        private sealed class ManualTimer(TimerCallback callback, object? state, DateTimeOffset deadline) : ITimer
        {
            internal DateTimeOffset Deadline => deadline;
            internal bool Disposed { get; private set; }
            internal void Fire() => callback(state);
            public bool Change(TimeSpan dueTime, TimeSpan period) => throw new NotSupportedException();
            public void Dispose() => Disposed = true;
            public ValueTask DisposeAsync() { Dispose(); return ValueTask.CompletedTask; }
        }
    }
}
