using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class SnapshotTests
{
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
            RawRepositoryEntry.FromText("D5/S0/Carrier/Ring.lean", "a"),
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
