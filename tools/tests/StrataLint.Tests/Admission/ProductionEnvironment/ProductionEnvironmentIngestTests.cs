using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void DirectoryLedgerReplacementWritesChangedSourceMetadataOnly()
    {
        var files = DirectoryLedgerTestSupport.Project(new RuleFixture().Files);
        var raw = RawRepositorySnapshot.Create(files.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var decoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var current = BackfillInventoryLoader.Load(decoded);
        var source = Assert.Single(current.RequireDigestionSources());
        var replacement = current.WithDigestionSources([
            source with { AcknowledgedStale = [source.Entries[0].AtomId] },
        ]);
        var unchangedAtom = raw.Entries.Single(entry => entry.Path.EndsWith(
            $"/{source.Entries[0].AtomId}.yaml",
            StringComparison.Ordinal));

        var replaced = IngestCommand.ReplaceLedger(
            raw,
            current,
            replacement);
        var redecoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(replaced)).Snapshot;
        var written = BackfillInventoryLoader.Load(redecoded);

        Assert.Equal(
            [source.Entries[0].AtomId],
            Assert.Single(written.RequireDigestionSources()).AcknowledgedStale.ToArray());
        Assert.Equal(
            unchangedAtom.Bytes.ToArray(),
            replaced.Entries.Single(entry => entry.Path == unchangedAtom.Path).Bytes.ToArray());
    }
}
