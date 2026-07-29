using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class CapacityPolicyTests
{
    // GREEN: the tracked working tree must already satisfy SL-003. This is the net
    // that fails in `dotnet test` — before push — when an artifact grows past the
    // hard line limit or a directory grows past the file limit.
    [Fact]
    public void RepositorySatisfiesCapacityLimits()
    {
        var findings = CapacityPolicy.InspectRepository(RepositoryLayout.FindRoot());

        Assert.True(
            findings.Count == 0,
            "SL-003 capacity violations (split the artifact or bucket the directory; run `make preflight` before pushing):"
                + Environment.NewLine
                + string.Join(
                    Environment.NewLine,
                    findings.Select(static finding => $"{finding.Path}: {finding.Message}")));
    }

    // RED: an artifact one line past the hard limit must be flagged.
    [Fact]
    public void OversizeArtifactIsRejectedByRedFixture()
    {
        var oversize = string.Join(
            '\n',
            Enumerable.Range(0, RepositoryRules.ArtifactHardLineLimit + 1)
                .Select(static i => $"line {i}"));

        var finding = Assert.Single(CapacityPolicy.InspectFiles(
            new[] { ("D5/S0/Carrier/Synthetic.lean", oversize) }));

        Assert.Equal("D5/S0/Carrier/Synthetic.lean", finding.Path);
        Assert.Contains("hard limit", finding.Message, StringComparison.Ordinal);
    }

    // RED: a directory one file past the limit must be flagged.
    [Fact]
    public void OverfullDirectoryIsRejectedByRedFixture()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryFileLimit + 1)
            .Select(static i => ($"Synthetic/Bucket/File{i}.cs", "x"))
            .ToArray();

        var finding = Assert.Single(CapacityPolicy.InspectFiles(files));

        Assert.Equal("Synthetic/Bucket", finding.Path);
        Assert.Contains("maximum", finding.Message, StringComparison.Ordinal);
    }

    // The exclusion set (theory inputs, Lake manifest, backfill inventory, CAS
    // blobs) must remain unbounded — an oversize excluded path is not a finding.
    [Fact]
    public void ExcludedArtifactIsNotBounded()
    {
        var oversize = string.Join(
            '\n',
            Enumerable.Range(0, RepositoryRules.ArtifactHardLineLimit + 1)
                .Select(static i => $"line {i}"));

        var findings = CapacityPolicy.InspectFiles(
            new[] { (BackfillInventoryRelativePath, oversize) });

        Assert.Empty(findings);
    }

    // The backfill inventory path, restated here only to exercise the exclusion;
    // the enforcement source is RepositoryRules.IsCapacityExcluded.
    private const string BackfillInventoryRelativePath = "Meta/BACKFILL.yaml";
}
