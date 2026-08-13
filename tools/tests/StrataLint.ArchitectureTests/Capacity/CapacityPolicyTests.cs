using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class CapacityPolicyTests
{
    // GREEN: SL-003's admission rule owns the per-change line and touched-directory
    // limits. This test keeps the separate full-repository tolerance net for buckets
    // that can overflow only after concurrent changes are combined.
    [Fact]
    public void RepositoryDirectoriesStayWithinCapacityTolerance()
    {
        var findings = CapacityPolicy.InspectRepository(RepositoryLayout.FindRoot())
            .Where(static finding => finding.Message.StartsWith("directory contains", StringComparison.Ordinal))
            .ToArray();

        Assert.True(
            findings.Length == 0,
            "SL-003 repository directory tolerance violations (split the bucket):"
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

    // RED: a directory past the repository tolerance must be flagged. The admission rule
    // still refuses at DirectoryFileLimit; this net exists so that a union produced by two
    // concurrent additions - which admission cannot see, because strict is forbidden (19)
    // and each PR judges its own tree - does not turn the whole repository red and block
    // every unrelated PR. Inside the band the bucket is over pressure and must be split,
    // and the next change touching it is refused at admission, which is where the split
    // pressure belongs.
    [Fact]
    public void DirectoryPastToleranceIsRejectedByRedFixture()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryToleranceLimit + 1)
            .Select(static i => ($"Synthetic/Bucket/File{i}.cs", "x"))
            .ToArray();

        var finding = Assert.Single(CapacityPolicy.InspectFiles(files));

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

        Assert.Empty(CapacityPolicy.InspectFiles(files));
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

    // Atomizer dialect rules are one canonical registry consumed through the
    // strict loader, not a navigated content artifact to split at an arbitrary line.
    [Fact]
    public void TheoryAtomizerDataRegistryIsNotBounded()
    {
        var oversize = string.Join(
            '\n',
            Enumerable.Range(0, RepositoryRules.ArtifactHardLineLimit + 1)
                .Select(static i => $"line {i}"));

        var findings = CapacityPolicy.InspectFiles(
            new[] { (TheoryAtomizerDataLoader.DataPath, oversize) });

        Assert.Empty(findings);
    }

    // Emitted Blueprint projections (FILEMAP kind=generated, produced by
    // ScribeEmitter) are photographs of the graph, not
    // skeleton: each document already pays its structural slot through its
    // .scribe.cs source. Bounding the projections halves the effective bucket:
    // the document GID must name an existing Lean module and the definition
    // path is bijective with that GID, so a lawful twelve-module Lean bucket
    // overflows its Blueprint mirror at the seventh blueprinted module.
    [Fact]
    public void EmittedBlueprintProjectionIsNotBounded()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryFileLimit + 1)
            .Select(static i => ($"Blueprint/D5/S1/Synthetic/File{i}.md", "x"))
            .ToArray();

        Assert.Empty(CapacityPolicy.InspectFiles(files));
    }

    // The canonical definition sources beside those projections stay bounded.
    [Fact]
    public void BlueprintDefinitionSourcesRemainBounded()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryToleranceLimit + 1)
            .Select(static i => ($"Blueprint/D5/S1/Synthetic/File{i}.scribe.cs", "x"))
            .ToArray();

        var finding = Assert.Single(CapacityPolicy.InspectFiles(files));

        Assert.Equal("Blueprint/D5/S1/Synthetic", finding.Path);
        Assert.Contains("tolerance", finding.Message, StringComparison.Ordinal);
    }

    // Formalization receipts accrue one file per admitted unit; the directory is a
    // machine inventory, never a navigated content bucket, so thirteen receipts must
    // not trip the directory file limit.
    [Fact]
    public void FormalizationReceiptInventoryIsNotBoundedByDirectoryLimit()
    {
        var receipts = Enumerable.Range(0, RepositoryRules.DirectoryFileLimit + 1)
            .Select(static i => (
                $"Meta/Digestion/formalizations/atom-{i:x2}.v1.json",
                "{}"))
            .ToArray();

        var findings = CapacityPolicy.InspectFiles(receipts);

        Assert.Empty(findings);
    }

    // The backfill inventory path, restated here only to exercise the exclusion;
    // the enforcement source is RepositoryRules.IsCapacityExcluded.
    private const string BackfillInventoryRelativePath = "Meta/BACKFILL.yaml";
}
