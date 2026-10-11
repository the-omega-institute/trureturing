using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe.Tests;

public sealed class GeneratedArtifactInventoryTests
{
    [Fact]
    public void InventoryProducersAgreeWithActualEmittersAndArtifactIdsRemainStable()
    {
        Assert.Equal(nameof(ScribeEmitter), GeneratedArtifactInventory.DocumentProducer);
        Assert.Equal(nameof(ValuesEmitter), GeneratedArtifactInventory.Values.Producer);
        Assert.Equal(nameof(DagEmitter), GeneratedArtifactInventory.Dag.Producer);
        Assert.Equal(nameof(DagEmitter), GeneratedArtifactInventory.TruthGraph.Producer);
        Assert.Equal(TruthExportModel.ProducerName, GeneratedArtifactInventory.TruthExport.Producer);
        Assert.Equal(nameof(FileMapEmitter), GeneratedArtifactInventory.FileMap.Producer);
        Assert.Equal(nameof(ScribeEmitter), GeneratedArtifactInventory.ScribeAttestation.Producer);
        Assert.Equal(
            ["A-DAG", "A-FILEMAP", "A-SCRIBE", "A-TRUTH", "A-TRUTHEXPORT", "A-VALUES"],
            GeneratedArtifactInventory.Create([]).Select(item => item.ArtifactId).Order(StringComparer.Ordinal));
    }

    [Fact]
    public void SnapshotDigestExcludesExactlyTheSharedInventoryAndRetainsOtherSourceBytes()
    {
        const string document = "Blueprint/synthetic.md";
        var entries = GeneratedArtifactInventory.Create([document])
            .Select(item => RawRepositoryEntry.FromText(item.Path, "projection\n"))
            .Append(RawRepositoryEntry.FromText("source.cs", "source\n")).ToArray();
        static RepositorySnapshot Decode(IEnumerable<RawRepositoryEntry> values) =>
            Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(RawRepositorySnapshot.Create(values))).Snapshot;
        var digest = SnapshotContentDigest.Compute(Decode(entries), [document]);
        var projected = entries.Select(entry => entry.Path == "source.cs" ? entry
            : RawRepositoryEntry.FromText(entry.Path, "changed projection\n"));
        Assert.Equal(digest, SnapshotContentDigest.Compute(Decode(projected), [document]));
        var changedSource = entries.Select(entry => entry.Path == "source.cs"
            ? RawRepositoryEntry.FromText(entry.Path, "changed source\n") : entry);
        Assert.NotEqual(digest, SnapshotContentDigest.Compute(Decode(changedSource), [document]));
        Assert.NotEqual(digest, SnapshotContentDigest.Compute(Decode(entries), []));
    }
}
