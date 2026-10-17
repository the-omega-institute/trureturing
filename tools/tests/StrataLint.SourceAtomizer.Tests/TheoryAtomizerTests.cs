using System.Text;
using StrataLint.Engine;
using static StrataLint.TestSupport.TheoryAtomizerAssertions;

namespace StrataLint.SourceAtomizer.Tests;

public sealed class TheoryAtomizerTests
{
    [Theory]
    [InlineData("PERIODIC_TREE.md", "证明")]
    [InlineData("ORDERED_SIMPLEX_L2_PROJECTION.md", "*Proof.*")]
    public void CurrentGenericSourcesPreserveBytesIdentityAndProofOwnership(string name, string proofMarker)
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, "docs/develop/theory", name));
        var document = AtomizerRegistry.Atomize(AtomizerRegistry.GenericId, bytes);
        Assert.NotEmpty(document.Claims);
        Assert.Equal(bytes, document.Reassemble().ToArray());
        Assert.Equal(document.Claims.Select(atom => atom.Fingerprints),
            GenericAtomizer.Atomize(bytes).Claims.Select(atom => atom.Fingerprints));
        Assert.All(document.Claims, atom =>
        {
            AssertContentIdentity(atom);
            Assert.Equal(bytes[atom.StartByte..atom.EndByte], atom.RawBytes.ToArray());
        });
        Assert.Contains(document.Claims, atom => Encoding.UTF8.GetString(atom.RawBytes.AsSpan())
            .Contains(proofMarker, StringComparison.Ordinal));
    }

    [Fact]
    public void GenericDuplicateClaimsShareIdentityAndRetainSeparateOccurrences()
    {
        const string claim = "**定理 1.1** α = α。\n\n*证明。* 恒等。\n\n";
        var document = GenericAtomizer.Atomize(Encoding.UTF8.GetBytes(claim + claim));
        Assert.Equal(2, document.Claims.Length);
        Assert.Equal(document.Claims[0].Fingerprints, document.Claims[1].Fingerprints);
        Assert.NotEqual(document.Claims[0].StartByte, document.Claims[1].StartByte);
        Assert.All(document.Claims, atom => Assert.Contains("*证明。*", Encoding.UTF8.GetString(atom.RawBytes.AsSpan())));
    }
    [Fact]
    public void ParserSourceSelectionRequiresDeclaredPolicy()
    {
        const string path = "docs/develop/theory/UNDECLARED.md";
        var raw = RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(path, "## Claim 1\n\nText.\n")]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        Assert.False(DigestionSourceEligibility.IsEligible(snapshot, path));
        Assert.Empty(DigestionIngestor.RegisterDefaultTheorySources(
            BackfillInventoryDocument.Create([], []), snapshot).RequireDigestionSources());
    }

    [Theory]
    [InlineData("wm-v1")]
    [InlineData("cone-v1")]
    [InlineData("gict-v1")]
    [InlineData("pzg-v1")]
    [InlineData("observer-v1")]
    [InlineData("periodic-tree-v1")]
    [InlineData("dialect:qdo")]
    [InlineData("dialect:arbitrary")]
    [InlineData("none")]
    [InlineData("unknown")]
    public void UnsupportedFormatsFailBeforeParserOrWriter(string format)
    {
        Assert.Equal(new[] { "generic-v1" }, AtomizerRegistry.RegisteredIds.ToArray());
        Assert.False(AtomizerRegistry.IsRegistered(format));
        Assert.Throws<FormatException>(() => AtomizerRegistry.Atomize(format, "**定理 1.1** valid Markdown"u8));
        var atom = DigestionAtom.FromFrozenCas([.. "α\nβ\n"u8.ToArray()]);
        var entry = DigestionTestSupport.Entry(atom, atom.Fingerprints.RawSha256[7..], format);
        Assert.Throws<FormatException>(() => DigestionDecomposition.Plan(entry, atom.RawBytes,
            GenericAtomizer.Atomize));
    }

}
