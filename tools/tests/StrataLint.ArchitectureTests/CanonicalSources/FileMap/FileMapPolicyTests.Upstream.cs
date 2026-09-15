using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void UpstreamProbeSourceHasWriterVerifierAndContentRegistration()
    {
        var manifest = Parse(Entry("Meta/Digestion/upstream/**", "data", "SettleUpstreamCommand", "DigestionStatusEvaluator", "DigestionStatusEvaluator")
            .Replace("admission_plane = \"judge\"", "admission_plane = \"content\"", StringComparison.Ordinal));
        var entry = Assert.Single(manifest.Match("Meta/Digestion/upstream/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.lean"));
        Assert.Equal("Meta/Digestion/upstream/**", entry.Pattern);
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal(FileMapAdmissionPlane.Content, entry.AdmissionPlane);
        Assert.Equal("SettleUpstreamCommand", entry.ProducedBy);
        Assert.Equal(new[] { "DigestionStatusEvaluator" }, entry.ConsumedBy.ToArray());
        Assert.Equal(new[] { "DigestionStatusEvaluator" }, entry.VerifiedBy.ToArray());
        Assert.Equal("none", entry.ArtifactId);
        Assert.Equal("committed-source", entry.RuntimeDisposition);
        Assert.Null(RepositoryPathPolicy.Validate(
            RepoPath.CreateKnown("Meta/Digestion/upstream/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.lean"),
            SyntheticRegistry().Policy));
        // The FILEMAP strict loader and FileMapPolicy rules enforce the real registration at admission time.
    }

    [Theory]
    [InlineData("Meta/Digestion/stray.lean")]
    [InlineData("Meta/Digestion/upstream/not-an-id.lean")]
    [InlineData("Meta/Digestion/upstream/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.txt")]
    [InlineData("Meta/Digestion/upstream/nested/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.lean")]
    public void UpstreamPathAdmissionDoesNotPermitStrayFiles(string path)
    {
        Assert.NotNull(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), SyntheticRegistry().Policy));
    }

    [Fact]
    public void OptionalProbeFamilyCanBeEmptyAfterClearingLastReceipt()
    {
        var manifest = Parse(Entry("Meta/Digestion/upstream/**", "data", "SettleUpstreamCommand", "DigestionStatusEvaluator", "DigestionStatusEvaluator")
            .Replace("admission_plane = \"judge\"", "admission_plane = \"content\"", StringComparison.Ordinal));
        Assert.Empty(FileMapPolicy.InspectPatternPopulation(manifest, []));
        Assert.Single(FileMapPolicy.InspectPatternPopulation(Parse(Entry("Meta/Digestion/stray/**", "data", "SettleUpstreamCommand", "DigestionStatusEvaluator", "DigestionStatusEvaluator")), []));
    }
}
