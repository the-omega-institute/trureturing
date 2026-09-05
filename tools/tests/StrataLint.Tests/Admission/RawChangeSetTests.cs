using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RawChangeSetTests
{
    [Fact]
    public void ContainsPathUsesOrdinalPathIdentityAndPreservesKinds()
    {
        var changes = RawChangeSet.CreateWithKinds(
        [
            ("D5/Alpha.lean", RawChangeKind.Added),
            ("D5/Beta.lean", RawChangeKind.Deleted),
        ]);
        Assert.True(changes.ContainsPath("D5/Alpha.lean"));
        Assert.True(changes.ContainsPath("D5/Beta.lean"));
        Assert.False(changes.ContainsPath("D5/Missing.lean"));
        Assert.False(changes.ContainsPath("d5/Alpha.lean"));
        Assert.Equal(
            [RawChangeKind.Added, RawChangeKind.Deleted],
            changes.Entries.Select(static entry => entry.Kind));
        Assert.Equal(
            ["D5/Alpha.lean", "D5/Beta.lean"],
            changes.Entries.Select(static entry => entry.Path.Value));
        Assert.Equal(
            ["D5/Alpha.lean", "D5/Beta.lean"],
            changes.Paths.Select(static path => path.Value));
    }
}
