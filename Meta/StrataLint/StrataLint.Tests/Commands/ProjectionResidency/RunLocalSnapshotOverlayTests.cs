using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RunLocalSnapshotOverlayTests
{
    [Fact]
    public void VerifiedReceiptSuppliesRunLocalArtifactBytes()
    {
        using var fixture = new OverlayFixture();
        var produced = fixture.Produce();

        var overlaid = RunLocalSnapshotOverlay.Apply(
            RawRepositorySnapshot.Create([]),
            fixture.OutputRoot,
            produced.RequestSha256,
            fixture.Inventory);

        var entry = Assert.Single(overlaid.Entries);
        Assert.Equal(fixture.ArtifactPath, entry.Path);
        Assert.True(fixture.ArtifactBytes.AsSpan().SequenceEqual(entry.Bytes.AsSpan()));
    }

    [Fact]
    public void MissingReceiptFailsClosed()
    {
        using var fixture = new OverlayFixture();

        var exception = Assert.Throws<InvalidOperationException>(() =>
            RunLocalSnapshotOverlay.Apply(
                RawRepositorySnapshot.Create([]),
                fixture.OutputRoot,
                new string('a', 64),
                fixture.Inventory));

        Assert.Contains("RUN_LOCAL_RECEIPT_INVALID", exception.Message, StringComparison.Ordinal);
        Assert.Contains("handle is missing", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void TamperedArtifactBytesFailClosed()
    {
        using var fixture = new OverlayFixture();
        var produced = fixture.Produce();
        File.WriteAllText(
            Path.Combine(fixture.OutputRoot, OverlayFixture.RunId, fixture.ArtifactPath),
            "tampered\n");

        var exception = Assert.Throws<InvalidOperationException>(() =>
            RunLocalSnapshotOverlay.Apply(
                RawRepositorySnapshot.Create([]),
                fixture.OutputRoot,
                produced.RequestSha256,
                fixture.Inventory));

        Assert.Contains("RUN_LOCAL_RECEIPT_INVALID", exception.Message, StringComparison.Ordinal);
        Assert.Contains("artifact bytes mismatch", exception.Message, StringComparison.Ordinal);
    }

    private sealed class OverlayFixture : IDisposable
    {
        internal const string RunId = "0123456789abcdef0123456789abcdef";
        internal string ArtifactPath { get; } = "Generated/example.json";
        internal ImmutableArray<byte> ArtifactBytes { get; } = [1, 2, 3, 4];
        internal string SourceRoot { get; } = Path.Combine(Path.GetTempPath(), "overlay-source-" + Guid.NewGuid().ToString("N"));
        internal string OutputRoot { get; } = Path.Combine(Path.GetTempPath(), "overlay-output-" + Guid.NewGuid().ToString("N"));
        internal ImmutableArray<RunArtifactInventoryItem> Inventory { get; }

        internal OverlayFixture()
        {
            Directory.CreateDirectory(Path.Combine(SourceRoot, "Generated"));
            Directory.CreateDirectory(OutputRoot);
            File.WriteAllBytes(Path.Combine(SourceRoot, ArtifactPath), ArtifactBytes.AsSpan());
            Inventory = [new RunArtifactInventoryItem("A-EXAMPLE", ArtifactPath, "100644")];
        }

        internal RunProtocolResult Produce()
        {
            var request = RunHandleJson.Write(new Dictionary<string, object?>
            {
                ["schema"] = "run-request-v1",
                ["run_id"] = RunId,
                ["source_tree_sha256"] = new string('a', 64),
                ["base_tree_sha256"] = new string('b', 64),
                ["producer_build_sha256"] = new string('c', 64),
                ["source_date_epoch"] = 0,
                ["expected_artifact_inventory_sha256"] = RunHandleDigests.Inventory(Inventory),
            });
            var produced = RunHandleProducer.Produce(SourceRoot, OutputRoot, request, Inventory);
            Assert.Equal(0, produced.ExitCode);
            return produced;
        }

        public void Dispose()
        {
            Directory.Delete(SourceRoot, recursive: true);
            Directory.Delete(OutputRoot, recursive: true);
        }
    }
}
