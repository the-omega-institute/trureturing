using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeTestMapDeriverProjectionTests
{
    [Fact]
    public void ProjectionExternalByteChangesDoNotChangeSnapshotDerivationKey()
    {
        var first = Snapshot(
            ("src/App.cs", "internal sealed class App;\n"),
            ("README.md", "first\n"));
        var second = Snapshot(
            ("src/App.cs", "internal sealed class App;\n"),
            ("README.md", "second\n"));

        var firstKey = ScribeTestMapDeriver.SnapshotDerivationKey(
            ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(first));
        var secondKey = ScribeTestMapDeriver.SnapshotDerivationKey(
            ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(second));

        Assert.Equal(firstKey, secondKey);
    }

    [Fact]
    public void SparseAndFullProjectionModesHaveDifferentSnapshotDerivationKeys()
    {
        var snapshot = Snapshot(("src/App.cs", "internal sealed class App;\n"));
        var sparse = ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(snapshot);
        var full = EffectiveDerivationInputProjection.Full(snapshot);

        Assert.NotEqual(
            ScribeTestMapDeriver.SnapshotDerivationKey(sparse),
            ScribeTestMapDeriver.SnapshotDerivationKey(full));
    }

    [Fact]
    public void ProjectionInputByteChangesChangeSnapshotDerivationKey()
    {
        var first = Snapshot(("src/App.cs", "internal sealed class App;\n"));
        var second = Snapshot(("src/App.cs", "internal sealed class Changed;\n"));

        Assert.NotEqual(
            ScribeTestMapDeriver.SnapshotDerivationKey(
                ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(first)),
            ScribeTestMapDeriver.SnapshotDerivationKey(
                ScribeTestMapDeriver.CreateEffectiveDerivationInputProjection(second)));
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(static file =>
                RawRepositoryEntry.FromText(file.Path, file.Text))))).Snapshot;
}
