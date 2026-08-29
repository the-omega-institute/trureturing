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
    // and the next change introducing a capacity-counted path absent from its ForkPoint
    // is refused at admission, which is where the split pressure belongs.
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
    // 这张网的存在理由写在 CapacityPolicy 的注释里:「SL-003 has repeatedly slipped past
    // `dotnet test`」。但 InspectRepository 此前**没有任何调用者**——全部用例走 InspectFiles
    // 加合成 fixture,于是它从未对真仓库跑过。2026-08-15 实测该缺口的代价:dev 上
    // DigestionLedgerAligner.cs 达 823 行(硬线 800),而 `make -C tools test` 的
    // ArchitectureTests 仍 90/90 全绿;越线只在准入侧被发现,而准入是全仓阻断,于是
    // 每一个 PR(包括从未碰过该文件的 #1890/#1891/#1896/#1897)一起被判红,全仓锁死约一小时。
    //
    // 检测放在 dotnet test 里,阻断留给准入——这是第20条执法分级的形状:检测要早要廉,
    // 阻断要窄要准。缺了这一半,唯一的执法手段就只剩最贵的那个。
    [Fact]
    public void RepositoryHasNoOversizeArtifactOrOverfullDirectory()
    {
        const string productionEnvironmentBucket =
            "tools/tests/StrataLint.Tests/Admission/ProductionEnvironment";
        var directMembers = GitIndexRepositoryFiles.Enumerate(RepositoryLayout.FindRoot())
            .Select(static file => file.RelativePath)
            .Where(path => path.StartsWith(productionEnvironmentBucket + "/", StringComparison.Ordinal))
            .Where(path => !path[(productionEnvironmentBucket.Length + 1)..].Contains('/'))
            .ToArray();

        Assert.True(
            directMembers.Length <= RepositoryRules.DirectoryFileLimit,
            $"{productionEnvironmentBucket} contains {directMembers.Length} direct files");
        Assert.Empty(CapacityPolicy.InspectRepository(RepositoryLayout.FindRoot()));
    }


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
