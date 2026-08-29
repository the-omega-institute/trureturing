using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class CapacityPolicyTests
{
    // RED: an artifact one line past the hard limit must be flagged.
    [Fact]
    public void OversizeArtifactIsRejectedByRedFixture()
    {
        var oversize = string.Join(
            '\n',
            Enumerable.Range(0, RepositoryRules.ArtifactHardLineLimit + 1)
                .Select(static i => $"line {i}"));

        var finding = Assert.Single(RepositoryCapacityAudit.InspectFiles(
            new[] { ("D5/S0/Carrier/Synthetic.lean", oversize) }));

        Assert.Equal("D5/S0/Carrier/Synthetic.lean", finding.Path);
        Assert.Contains("hard limit", finding.Message, StringComparison.Ordinal);
    }

    // RED: a directory past the repository tolerance must be flagged. The admission rule
    // still refuses at DirectoryFileLimit; this net exists so that a union produced by two
    // concurrent additions - which admission cannot see, because strict is forbidden (19)
    // and each PR judges its own tree - does not turn the whole repository red and block
    // every unrelated PR. Inside the band the bucket is over pressure and must be split,
    // and the next change introducing a capacity-counted path absent from its ForkPoint
    // is refused at admission, which is where the split pressure belongs.
    [Fact]
    public void DirectoryPastToleranceIsRejectedByRedFixture()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryToleranceLimit + 1)
            .Select(static i => ($"Synthetic/Bucket/File{i}.cs", "x"))
            .ToArray();

        var finding = Assert.Single(RepositoryCapacityAudit.InspectFiles(files));

        Assert.Equal("Synthetic/Bucket", finding.Path);
        Assert.Contains("tolerance", finding.Message, StringComparison.Ordinal);
    }

    // The band itself: a union one past the admission limit is tolerated repository-wide,
    // which is the whole point - otherwise two concurrent merges red the repository.
    [Fact]
    public void UnionOneFilePastAdmissionLimitIsToleratedRepositoryWide()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryFileLimit + 1)
            .Select(static i => ($"Synthetic/Bucket/File{i}.cs", "x"))
            .ToArray();

        Assert.Empty(RepositoryCapacityAudit.InspectFiles(files));
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

        var findings = RepositoryCapacityAudit.InspectFiles(
            new[] { (BackfillInventoryRelativePath, oversize) });

        Assert.Empty(findings);
    }

    // Atomizer dialect rules are one canonical registry consumed through the
    // strict loader, not a navigated content artifact to split at an arbitrary line.
    [Fact]
    public void TheoryAtomizerDataRegistryIsNotBounded()
    {
        var oversize = string.Join(
            '\n',
            Enumerable.Range(0, RepositoryRules.ArtifactHardLineLimit + 1)
                .Select(static i => $"line {i}"));

        var findings = RepositoryCapacityAudit.InspectFiles(
            new[] { (TheoryAtomizerDataLoader.DataPath, oversize) });

        Assert.Empty(findings);
    }

    // Generated Blueprint Markdown projections are not a second structural slot:
    // each document already pays that slot through its .scribe.cs source at the
    // same stem. This is a capacity fact only; it gives Markdown no content or
    // history authority.
    [Fact]
    public void GeneratedBlueprintMarkdownProjectionIsNotBounded()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryFileLimit + 1)
            .Select(static i => ($"Blueprint/D5/S1/Synthetic/File{i}.md", "x"))
            .ToArray();

        Assert.Empty(RepositoryCapacityAudit.InspectFiles(files));
    }

    // The canonical definition sources beside those projections stay bounded.
    [Fact]
    public void BlueprintDefinitionSourcesRemainBounded()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryToleranceLimit + 1)
            .Select(static i => ($"Blueprint/D5/S1/Synthetic/File{i}.scribe.cs", "x"))
            .ToArray();

        var finding = Assert.Single(RepositoryCapacityAudit.InspectFiles(files));

        Assert.Equal("Blueprint/D5/S1/Synthetic", finding.Path);
        Assert.Contains("tolerance", finding.Message, StringComparison.Ordinal);
    }

    // Formalization receipts accrue one file per admitted unit; the directory is a
    // machine inventory, never a navigated content bucket, so one receipt past the
    // admission limit must not trip the directory file limit.
    [Fact]
    public void FormalizationReceiptInventoryIsNotBoundedByDirectoryLimit()
    {
        var receipts = Enumerable.Range(0, RepositoryRules.DirectoryFileLimit + 1)
            .Select(static i => (
                $"Meta/Digestion/formalizations/atom-{i:x2}.v1.json",
                "{}"))
            .ToArray();

        var findings = RepositoryCapacityAudit.InspectFiles(receipts);

        Assert.Empty(findings);
    }

    // The backfill inventory path, restated here only to exercise the exclusion;
    // the enforcement source is RepositoryRules.IsCapacityExcluded.
    private const string BackfillInventoryRelativePath = "Meta/BACKFILL.yaml";

    // Pinned by the owner's 2026-08-30 ruling (放宽到 24、48): admission limit 24, repository
    // tolerance 48. The tolerance band stays exactly one admission limit wide so that two PRs
    // branched from the same base can each fill a bucket to the limit and their union still
    // clears the repository-wide net (see DirectoryToleranceLimit in RepositoryRules.Structure.cs).
    [Fact]
    public void DirectoryCapacityThresholdsArePinnedToTheAdjudicatedValues()
    {
        Assert.Equal(24, RepositoryRules.DirectoryFileLimit);
        Assert.Equal(48, RepositoryRules.DirectoryToleranceLimit);
        Assert.Equal(2 * RepositoryRules.DirectoryFileLimit, RepositoryRules.DirectoryToleranceLimit);
    }
}
