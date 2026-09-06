using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class DigestAtomAgeTests
{
    [Theory]
    [InlineData(6, "<7")]
    [InlineData(7, "7-13")]
    [InlineData(13, "7-13")]
    [InlineData(14, "14-29")]
    [InlineData(29, "14-29")]
    [InlineData(30, "30-44")]
    [InlineData(44, "30-44")]
    [InlineData(45, ">=45")]
    public void StatusAgeUsesUtcCalendarDayAtEveryBucketBoundary(int days, string bucket)
    {
        var fixture = DigestAgeFixture.Create();
        var firstSeen = new DateTimeOffset(2026, 9, 6, 23, 59, 0, TimeSpan.Zero).AddDays(-days);
        var history = new FakeAtomHistorySource(() => new AtomHistory(false,
            new Dictionary<string, DateTimeOffset> { [fixture.AtomIds[0]] = firstSeen }));

        var result = fixture.Run(history);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var entry = Assert.Single(json.RootElement.GetProperty("frontier").GetProperty("entries").EnumerateArray());
        Assert.Equal(firstSeen.ToString("yyyy-MM-dd", System.Globalization.CultureInfo.InvariantCulture),
            entry.GetProperty("first_seen_date").GetString());
        Assert.Equal(days, entry.GetProperty("age_days").GetInt32());
        Assert.Equal(bucket, entry.GetProperty("age_bucket").GetString());
        var ledgerEntry = Assert.Single(json.RootElement.GetProperty("entries").EnumerateArray());
        Assert.Equal(days, ledgerEntry.GetProperty("age_days").GetInt32());
        Assert.Equal(1, history.Calls);
    }

    [Theory]
    [InlineData("--json")]
    [InlineData("--residual-summary")]
    public void AgeHistogramCountsSourcesAndPrimaryDispositionsWithoutChangingTreeBytes(string option)
    {
        var fixture = DigestAgeFixture.Create(3);
        var history = new FakeAtomHistorySource(() => new AtomHistory(false,
            new Dictionary<string, DateTimeOffset>
            {
                [fixture.AtomIds[0]] = new(2026, 9, 1, 0, 0, 0, TimeSpan.Zero),
                [fixture.AtomIds[1]] = new(2026, 7, 23, 0, 0, 0, TimeSpan.Zero),
                [fixture.AtomIds[2]] = new(2026, 8, 30, 0, 0, 0, TimeSpan.Zero),
            }));

        var result = fixture.Run(history, option);

        Assert.True(result.Success, result.Error);
        Assert.Equal(1, history.Calls);
        if (option == "--residual-summary")
        {
            Assert.Contains("## age", result.Output, StringComparison.Ordinal);
            Assert.Contains("| source-a | 1 | 1 | 0 | 0 | 0 | 2 | 2026-08-30 |", result.Output, StringComparison.Ordinal);
            Assert.Contains("| source-b | 0 | 0 | 0 | 0 | 1 | 1 | 2026-07-23 |", result.Output, StringComparison.Ordinal);
            Assert.Contains("| total | 1 | 1 | 0 | 0 | 1 | 3 | 2026-07-23 |", result.Output, StringComparison.Ordinal);
            Assert.Contains("| source-b | quarantined | 0 | 0 | 0 | 0 | 1 | 1 |", result.Output, StringComparison.Ordinal);
            return;
        }

        using var json = JsonDocument.Parse(result.Output);
        var histogram = json.RootElement.GetProperty("age_histogram");
        Assert.Equal(3, histogram.GetProperty("total").GetProperty("count").GetInt32());
        var sources = histogram.GetProperty("per_source").EnumerateArray().ToArray();
        Assert.Equal(2, sources.Length);
        Assert.Equal("source-a", sources[0].GetProperty("source_id").GetString());
        Assert.Equal(2, sources[0].GetProperty("count").GetInt32());
        Assert.Equal("2026-08-30", sources[0].GetProperty("oldest_first_seen_date").GetString());
        Assert.Equal(1, sources[0].GetProperty("buckets").GetProperty("<7").GetInt32());
        Assert.Equal(1, sources[0].GetProperty("buckets").GetProperty("7-13").GetInt32());
        Assert.Equal(1, sources[1].GetProperty("by_disposition").GetProperty("quarantined")
            .GetProperty(">=45").GetInt32());
        Assert.Equal(0, sources[1].GetProperty("by_disposition").GetProperty("quarantined")
            .GetProperty("<7").GetInt32());
    }

    [Fact]
    public void ShallowHistoryFailsClosedEvenWhenEveryAtomHasAnAddRecord()
    {
        var fixture = DigestAgeFixture.Create();
        var history = new FakeAtomHistorySource(() =>
            FakeAtomHistorySource.ForEntries(fixture.AtomIds).Read() with { IsShallow = true });

        var result = fixture.Run(history);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.StartsWith("DIGEST_AGE_HISTORY_UNAVAILABLE ", result.Error, StringComparison.Ordinal);
        Assert.Contains("shallow", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingAtomAddRecordFailsClosed()
    {
        var fixture = DigestAgeFixture.Create(2);
        var result = fixture.Run(FakeAtomHistorySource.ForEntries([fixture.AtomIds[0]]));

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.StartsWith("DIGEST_AGE_HISTORY_UNAVAILABLE ", result.Error, StringComparison.Ordinal);
        Assert.Contains(fixture.AtomIds[1], result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void HistoryTimeoutFailsClosedWithoutPartialOutput()
    {
        var fixture = DigestAgeFixture.Create();
        var result = fixture.Run(new FakeAtomHistorySource(() => throw new TimeoutException("git timed out")));

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.StartsWith("DIGEST_AGE_HISTORY_UNAVAILABLE ", result.Error, StringComparison.Ordinal);
        Assert.Contains("timed out", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ReadinessDoesNotReadAtomHistory()
    {
        var fixture = DigestAgeFixture.Create();
        var history = new FakeAtomHistorySource(() => throw new InvalidOperationException("unexpected history read"));

        var result = fixture.Run(history, "--readiness");

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, history.Calls);
    }
}
