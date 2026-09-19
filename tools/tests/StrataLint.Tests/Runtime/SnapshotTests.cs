using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class SnapshotTests
{
    [Theory]
    [InlineData("", false)]
    [InlineData("\n\n", false)]
    [InlineData("a\nb\n", false)]
    [InlineData("a b\n", false)]
    [InlineData("a\rb\n", false)]
    [InlineData("\tvalue", false)]
    [InlineData("\u00a0\n", false)]
    [InlineData(" ", true)]
    [InlineData("\t", true)]
    [InlineData("\r", true)]
    [InlineData("\r\n", true)]
    [InlineData("a \nb", true)]
    [InlineData("a\t\n\n", true)]
    [InlineData("a\n ", true)]
    [InlineData("\n\nb\r\n\n", true)]
    public void TrailingWhitespacePreservesLineEndingBoundaries(string text, bool expected)
    {
        var decoded = SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            [RawRepositoryEntry.FromText("sample.txt", text)]));

        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(decoded).Snapshot;
        Assert.Equal(expected, Assert.Single(snapshot.Files).Value.HasTrailingWhitespace);
    }

    [Fact]
    public void TrailingWhitespaceInspectionDoesNotAllocatePerLine()
    {
        var text = string.Concat(Enumerable.Repeat("no trailing whitespace\n", 100_000));
        var path = RepoPath.CreateKnown("large.txt");
        var bytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(text));
        _ = new RepositoryFile(path, bytes, "warm\nup\n");

        var before = GC.GetAllocatedBytesForCurrentThread();
        var file = new RepositoryFile(path, bytes, text);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.False(file.HasTrailingWhitespace);
        Assert.True(allocated < text.Length,
            $"Whitespace inspection allocated {allocated} bytes for {text.Length} existing characters.");
    }

    [Fact]
    public void TheoryBytesAreOpaqueAndPreserveInvalidUtf8Exactly()
    {
        var path = string.Concat("docs/develop/", "theory/non-utf8.bin");
        var bytes = ImmutableArray.Create<byte>(0xff, 0x00, 0xfe);
        var raw = RawRepositorySnapshot.Create(
        [
            new RawRepositoryEntry(path, bytes),
        ]);

        var decoded = SnapshotDecoder.Decode(raw);

        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(decoded).Snapshot;
        Assert.True(snapshot.TryGetFile(path, out var file));
        Assert.True(file.IsOpaque);
        Assert.Equal(bytes.ToArray(), file.RawBytes.ToArray());
    }

    [Fact]
    public void NoncanonicalCasNeighborRemainsStrictUtf8()
    {
        var raw = RawRepositorySnapshot.Create(
        [
            new RawRepositoryEntry(
                DigestionCasStore.RootPath + "not-a-hash",
                ImmutableArray.Create<byte>(0xff)),
        ]);

        var decoded = SnapshotDecoder.Decode(raw);

        var failure = Assert.IsType<SnapshotDecodeOutcome.InfrastructureFailure>(decoded);
        Assert.Contains("UTF-8", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SnapshotStrictlyDecodesUtf8WithoutErasingRawAnomalies()
    {
        var raw = RawRepositorySnapshot.Create(new[]
        {
            new RawRepositoryEntry(
                "Evidence/D5/S0/Carrier/Result.run.json",
                ImmutableArray.CreateRange(Encoding.UTF8.GetPreamble().Concat(Encoding.UTF8.GetBytes("{\"value\": 1} \r\n")))),
        });

        var decoded = SnapshotDecoder.Decode(raw);

        var accepted = Assert.IsType<SnapshotDecodeOutcome.Decoded>(decoded);
        var file = accepted.Snapshot.Files.Single().Value;
        Assert.True(file.HasBom);
        Assert.True(file.HasCarriageReturn);
        Assert.True(file.HasTrailingWhitespace);
        Assert.Equal(raw.Entries[0].Bytes.ToArray(), file.RawBytes.ToArray());
    }

    [Fact]
    public void SnapshotRejectsInvalidUtf8AsInfrastructureFailure()
    {
        var raw = RawRepositorySnapshot.Create(new[]
        {
            new RawRepositoryEntry("Evidence/D5/S0/Carrier/Result.run.json", ImmutableArray.Create<byte>(0xff)),
        });

        var decoded = SnapshotDecoder.Decode(raw);

        var failure = Assert.IsType<SnapshotDecodeOutcome.InfrastructureFailure>(decoded);
        Assert.Contains("UTF-8", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SnapshotRejectsCaseCollisionsAndTraversalBeforeRulesRun()
    {
        var collision = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText(RuleFixture.RingPath, "a"),
            RawRepositoryEntry.FromText("D5/S0/carrier/Ring.lean", "b"),
        });
        var traversal = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("../D5/S0/Carrier/Ring.lean", "a"),
        });

        Assert.IsType<SnapshotDecodeOutcome.InfrastructureFailure>(SnapshotDecoder.Decode(collision));
        Assert.IsType<SnapshotDecodeOutcome.InfrastructureFailure>(SnapshotDecoder.Decode(traversal));
    }
}
