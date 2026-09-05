using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class TruthGraphJsonTests
{
    [Fact]
    public void SnapshotIdentityIgnoresAllGeneratedProjectionBytes()
    {
        var documentPath = DocumentAssembly.Definitions[0].RelativePath.Value;
        var first = Snapshot(
            ("Meta/source.txt", "alpha\n"),
            (documentPath, "old document projection\n"),
            (DagEmitter.RelativePath, "old dag projection\n"),
            (DagEmitter.TruthGraphRelativePath, "old truth projection\n"),
            (ScribeEmitter.AttestationRelativePath, "old attestation\n"));
        var projectionsChanged = Snapshot(
            ("Meta/source.txt", "alpha\n"),
            (documentPath, "new document projection\n"),
            (DagEmitter.RelativePath, "new dag projection\n"),
            (DagEmitter.TruthGraphRelativePath, "new truth projection\n"),
            (ScribeEmitter.AttestationRelativePath, "new attestation\n"));
        var sourceChanged = Snapshot(
            ("Meta/source.txt", "beta\n"),
            (documentPath, "old document projection\n"),
            (DagEmitter.RelativePath, "old dag projection\n"),
            (DagEmitter.TruthGraphRelativePath, "old truth projection\n"),
            (ScribeEmitter.AttestationRelativePath, "old attestation\n"));
        var documentPaths = DocumentAssembly.Definitions
            .Select(static definition => definition.RelativePath.Value);

        Assert.Equal(
            SnapshotContentDigest.Compute(first, documentPaths),
            SnapshotContentDigest.Compute(projectionsChanged, documentPaths));
        Assert.NotEqual(
            SnapshotContentDigest.Compute(first, documentPaths),
            SnapshotContentDigest.Compute(sourceChanged, documentPaths));
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            files.Select(static file => RawRepositoryEntry.FromText(file.Path, file.Text))))).Snapshot;
}
