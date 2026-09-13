using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AtomHistoryParserTests
{
    [Fact]
    public void ReaddedPathUsesMinimumCommitterTimeInAnyTraversalOrder()
    {
        var fixture = DigestAgeFixture.Create();
        var path = DigestionCasStore.RootPath + fixture.AtomIds[0];
        var history = $"\u001e1788307200\n\n{path}\n\u001e1786665600\n\n{path}\n"
            + $"\u001e1787270400\n\n{path}\n";

        var result = fixture.Run(new FakeAtomHistorySource(() =>
            new AtomHistory(false, AtomHistoryParser.Parse(Encoding.UTF8.GetBytes(history)))));

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var entry = Assert.Single(json.RootElement.GetProperty("entries").EnumerateArray());
        Assert.Equal("2026-08-14", entry.GetProperty("first_seen_date").GetString());
        Assert.Equal(23, entry.GetProperty("age_days").GetInt32());
    }

    [Fact]
    public void MergeParentAdditionKeepsSideBranchDateRatherThanMergeDate()
    {
        var fixture = DigestAgeFixture.Create(2);
        var sidePath = DigestionCasStore.RootPath + fixture.AtomIds[0];
        var mainPath = DigestionCasStore.RootPath + fixture.AtomIds[1];
        // Separate-parent merge diffs repeat additions; the older side-parent commit follows.
        var history = $"\u001e1788307200\n\n{sidePath}\n\u001e1788307200\n\n{mainPath}\n"
            + $"\u001e1786665600\n\n{sidePath}\n\u001e1787270400\n\n{mainPath}\n";

        var result = fixture.Run(new FakeAtomHistorySource(() =>
            new AtomHistory(false, AtomHistoryParser.Parse(Encoding.UTF8.GetBytes(history)))));

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var entries = json.RootElement.GetProperty("entries").EnumerateArray();
        Assert.Equal("2026-08-14", entries.Single(entry =>
            entry.GetProperty("atom_id").GetString() == fixture.AtomIds[0])
            .GetProperty("first_seen_date").GetString());
    }

    [Theory]
    [InlineData("bad-time")]
    [InlineData("bad-path")]
    [InlineData("path-before-time")]
    [InlineData("truncated-path")]
    [InlineData("truncated-header")]
    [InlineData("invalid-utf8")]
    [InlineData("invalid-utf8-after-valid-record")]
    [InlineData("bad-later-time")]
    [InlineData("out-of-range-time")]
    public void MalformedOrTruncatedHistoryFailsClosed(string corruption)
    {
        var fixture = DigestAgeFixture.Create();
        var path = DigestionCasStore.RootPath + fixture.AtomIds[0];
        var text = corruption switch
        {
            "bad-time" => $"\u001eunknown\n\n{path}\n",
            "bad-path" => "\u001e1786665600\n\nMeta/Digestion/atoms/sha256/invalid\n",
            "path-before-time" => $"{path}\n",
            "truncated-path" => $"\u001e1786665600\n\n{path}",
            "truncated-header" => $"\u001e1786665600\n\n{path}\n\u001e178",
            "bad-later-time" => $"\u001e1786665600\n\n{path}\n\u001eunknown\n",
            "out-of-range-time" => $"\u001e9223372036854775807\n\n{path}\n",
            _ => $"\u001e1786665600\n\n{path}\n",
        };
        var bytes = corruption == "invalid-utf8" ? new byte[] { 0xff } : Encoding.UTF8.GetBytes(text);
        if (corruption == "invalid-utf8-after-valid-record") bytes = [.. bytes, 0xff, (byte)'\n'];

        var result = fixture.Run(new FakeAtomHistorySource(() =>
            new AtomHistory(false, AtomHistoryParser.Parse(bytes))));

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.StartsWith("DIGEST_AGE_HISTORY_UNAVAILABLE ", result.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(7)]
    [InlineData(8192)]
    public async Task StreamingAcrossRecordBoundariesPreservesMinimumTimes(int chunkBytes)
    {
        var firstId = new string('a', 64);
        var secondId = new string('b', 64);
        var first = DigestionCasStore.RootPath + firstId;
        var second = DigestionCasStore.RootPath + secondId;
        using var stream = new ShortReadStream(Encoding.UTF8.GetBytes(
            $"\u001e1788307200\n\n{first}\n{second}\n"
            + $"\u001e1786665600\n\n{first}\n"), chunkBytes);

        var result = await AtomHistoryParser.ParseAsync(stream, CancellationToken.None);

        Assert.Equal(2, result.Count);
        Assert.Equal(DateTimeOffset.FromUnixTimeSeconds(1786665600), result[firstId]);
        Assert.Equal(DateTimeOffset.FromUnixTimeSeconds(1788307200), result[secondId]);
    }

    [Fact]
    public async Task StreamingCancellationDoesNotReturnPartialHistory()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        using var stream = new MemoryStream(Encoding.UTF8.GetBytes("\u001e1786665600\n"));

        await Assert.ThrowsAnyAsync<OperationCanceledException>(() =>
            AtomHistoryParser.ParseAsync(stream, cancellation.Token));
    }

    private sealed class ShortReadStream(byte[] bytes, int chunkBytes) : MemoryStream(bytes, writable: false)
    {
        public override ValueTask<int> ReadAsync(Memory<byte> buffer, CancellationToken cancellation = default) =>
            base.ReadAsync(buffer[..Math.Min(chunkBytes, buffer.Length)], cancellation);
    }
}
