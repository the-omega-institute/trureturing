using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void UpstreamProbeSourceHasWriterVerifierAndContentRegistration()
    {
        var path = "Meta/Digestion/upstream/" + new string('a', 64) + ".lean";
        var manifest = FileMapLoader.LoadRepository(RepositoryLayout.FindRoot());
        var entry = Assert.Single(manifest.Match(path));
        Assert.Equal("Meta/Digestion/upstream/**", entry.Pattern);
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal(FileMapAdmissionPlane.Content, entry.AdmissionPlane);
        Assert.Equal("SettleUpstreamCommand", entry.ProducedBy);
        Assert.Equal(new[] { "DigestionStatusEvaluator" }, entry.ConsumedBy.ToArray());
        Assert.Equal(new[] { "DigestionStatusEvaluator" }, entry.VerifiedBy.ToArray());
        Assert.Equal("none", entry.ArtifactId);
        Assert.Equal("committed-source", entry.RuntimeDisposition);
        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), SyntheticRegistry().Policy));
        Assert.DoesNotContain(FileMapPolicy.InspectRepository(RepositoryLayout.FindRoot()), finding => finding.Path == entry.Pattern);
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
