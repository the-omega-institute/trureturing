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
            _ => $"\u001e1786665600\n\n{path}\n",
        };
        var bytes = corruption == "invalid-utf8" ? new byte[] { 0xff } : Encoding.UTF8.GetBytes(text);

        var result = fixture.Run(new FakeAtomHistorySource(() =>
            new AtomHistory(false, AtomHistoryParser.Parse(bytes))));

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.StartsWith("DIGEST_AGE_HISTORY_UNAVAILABLE ", result.Error, StringComparison.Ordinal);
    }
}
