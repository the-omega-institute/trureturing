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
        var containsPath = typeof(RawChangeSet).GetMethod(
            "ContainsPath",
            [typeof(string)]);
        Assert.NotNull(containsPath);

        Assert.True(Contains("D5/Alpha.lean"));
        Assert.True(Contains("D5/Beta.lean"));
        Assert.False(Contains("D5/Missing.lean"));
        Assert.False(Contains("d5/Alpha.lean"));
        Assert.Equal(
            [RawChangeKind.Added, RawChangeKind.Deleted],
            changes.Entries.Select(static entry => entry.Kind));
        Assert.Equal(
            ["D5/Alpha.lean", "D5/Beta.lean"],
            changes.Entries.Select(static entry => entry.Path.Value));
        Assert.Equal(
            ["D5/Alpha.lean", "D5/Beta.lean"],
            changes.Paths.Select(static path => path.Value));

        bool Contains(string path) =>
            Assert.IsType<bool>(containsPath.Invoke(changes, [path]));
    }
}
