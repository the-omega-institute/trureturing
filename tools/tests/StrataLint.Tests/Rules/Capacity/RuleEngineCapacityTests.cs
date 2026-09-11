using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleEngineCapacityTests
{
    private const int L = RepositoryRules.DirectoryFileLimit;

    [Fact]
    public void Sl003CapacityHardBlocksAtEightHundredAndSoftWarnsAtSixHundred()
    {
        // 600 < n <= 800: a non-blocking soft warning, not a rejection.
        var soft = new RuleFixture();
        soft.Files[RuleFixture.RingPath] += string.Concat(Enumerable.Repeat("-- pad\n", 700));
        var softDiag = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), soft.Build()).Diagnostics);
        Assert.Equal(AdmissionEffect.Observe, softDiag.AdmissionEffect);
        Assert.Equal(DisplaySeverity.Warning, softDiag.DisplaySeverity);
        Assert.Contains(
            $"soft limit {RepositoryRules.ArtifactSoftLineLimit}",
            softDiag.Message,
            StringComparison.Ordinal);

        // > 800: a hard block.
        var hard = new RuleFixture();
        hard.Files[RuleFixture.RingPath] += string.Concat(Enumerable.Repeat("-- pad\n", 801));
        var hardDiag = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), hard.Build()).Diagnostics);
        Assert.Equal(AdmissionEffect.Block, hardDiag.AdmissionEffect);
        Assert.Equal("artifact exceeds 800 lines", hardDiag.Message);
    }

    [Fact]
    public void Sl003DoesNotTreatTheSingleSourceDigestionLedgerAsASplittableModule()
    {
        var fixture = new RuleFixture();
        for (var index = 0; index < RepositoryRules.DirectoryFileLimit - 2; index++)
        {
            var path = $"Meta/Capacity{index:00}.txt";
            fixture.Files[path] = "fixture\n";
            fixture.Baseline[path] = "fixture\n";
        }

        fixture.Changes.Add("Meta/Capacity00.txt");
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;
        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.Path == "Meta");
    }

    [Fact]
    public void Sl003DoesNotTreatDirectoryDigestionLedgerFilesAsSplittableModules()
    {
        var fixture = new RuleFixture();

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;

        Assert.DoesNotContain(diagnostics, diagnostic =>
            BackfillInventoryLoader.IsCanonicalPath(diagnostic.Path));
    }

    [Fact]
    public void Sl003DoesNotTreatTheCasObjectStoreAsASplittableModule()
    {
        var fixture = new RuleFixture();
        for (var index = 0; index < (L + 1); index++)
        {
            var text = $"CAS object {index}\n";
            var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes(text));
            fixture.Files[captured.RelativePath] = text;
            // The change has to touch the store, or the capacity rule skips it for being
            // untouched and this stops testing the exclusion it is named for.
            fixture.Changes.Add(captured.RelativePath);
        }
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;
        Assert.DoesNotContain(diagnostics, diagnostic =>
            diagnostic.Path.StartsWith(DigestionCasStore.RootPath, StringComparison.Ordinal)
            || diagnostic.Path == DigestionCasStore.RootPath.TrimEnd('/'));
    }

    [Fact]
    public void Sl003DoesNotTreatAcceptedLedgerFragmentsAsASplittableModule()
    {
        var fixture = new RuleFixture();
        for (var index = 0; index < (L + 1); index++)
        {
            var identity = $"sha256:{index:x64}";
            var path = FrozenLedgerChangeClassifier.AcceptedPath(identity);
            fixture.Files[path] = "{}\n";
            fixture.Changes.Add(path);
        }
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;
        Assert.DoesNotContain(diagnostics, diagnostic =>
            diagnostic.Path == FrozenLedgerChangeClassifier.AcceptedRoot);
    }

    [Fact]
    public void Sl003DoesNotTreatTwentyFiveFrozenStateFragmentsAsASplittableModules()
    {
        var fixture = new RuleFixture();
        const string directory = "Golden/Frozen/state/D5/S3/Analytic/EulerGerm";
        for (var index = 0; index < 25; index++)
        {
            var path = $"{directory}/Module{index:00}.lean.json";
            fixture.Files[path] = $"{{\"statement_id\":\"sha256:{index:x64}\"}}\n";
            fixture.Changes.Add(path);
        }

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;

        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.Path == directory);
    }

    [Fact]
    public void Sl003DoesNotTreatCanonicalProblemPoolDossiersAsASplittableModule()
    {
        var fixture = new RuleFixture();
        for (var index = 1; index <= 60; index++)
        {
            var path = $"Problems/oeis-a000001-sample-slug-{index:0000}.md";
            fixture.Files[path] = "fixture\n";
            fixture.Changes.Add(path);
        }

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;

        Assert.Empty(diagnostics);
    }

    [Fact]
    public void Sl003StillBoundsCanonicalProblemPoolDossierLength()
    {
        var fixture = new RuleFixture();
        const string path = "Problems/oeis-a363560-cubic-ninth-power-substitution-mod-three.md";
        fixture.Baseline[path] = string.Empty;
        fixture.Files[path] = string.Concat(Enumerable.Repeat("pad\n", 900));
        fixture.Changes.Add(path);

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build()).Diagnostics);

        Assert.Equal(path, diagnostic.Path);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal("artifact exceeds 800 lines", diagnostic.Message);
    }

    [Fact]
    public void Sl003StillCountsNonCanonicalProblemPoolPaths()
    {
        var fixture = new RuleFixture();
        for (var index = 1; index <= 60; index++)
        {
            foreach (var path in new[] { $"Problems/Foo{index:0000}.md", $"Problems/sub/x{index:0000}.md" })
            {
                fixture.Files[path] = "fixture\n";
                fixture.Changes.Add(path);
            }
        }

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;

        foreach (var directory in new[] { "Problems", "Problems/sub" })
        {
            var diagnostic = Assert.Single(diagnostics, item => item.Path == directory);
            Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
            Assert.Contains("directory contains 60 files", diagnostic.Message, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Sl003RefusesNetGrowthOfAnOverfullBucket()
    {
        var fixture = OverfullBucket(baselineCount: (L - 1), currentCount: (L + 1));
        var changes = RawChangeSet.CreateWithKinds(
        [
            (OverfullMemberPath((L - 1)), RawChangeKind.Added),
            (OverfullMemberPath(L), RawChangeKind.Added),
        ]);
        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build(changes)).Diagnostics,
            item => item.Path == OverfullBucketPath);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(
            $"directory contains {L + 1} files (admission limit {RepositoryRules.DirectoryFileLimit}, "
            + $"repository tolerance {RepositoryRules.DirectoryToleranceLimit}; "
            + "split per CLAUDE.md 8)",
            diagnostic.Message);
    }

    [Fact]
    public void Sl003RefusesNewOverfullBucketAbsentFromBaseline()
    {
        var fixture = OverfullBucket(baselineCount: 0, currentCount: (L + 1));
        var changes = RawChangeSet.CreateWithKinds(
            Enumerable.Range(0, (L + 1))
                .Select(static index => (OverfullMemberPath(index), RawChangeKind.Added)));
        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build(changes)).Diagnostics,
            item => item.Path == OverfullBucketPath);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    [Fact]
    public void Sl003ObservesAModificationInsideAnOverfullBucket()
    {
        var fixture = OverfullBucket(baselineCount: (L + 1), currentCount: (L + 1));
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(0), RawChangeKind.Modified)]);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;
        AssertNonGrowingBucketIsObserved(diagnostics, (L + 1));
    }

    [Fact]
    public void Sl003ObservesADeletionThatLeavesTheBucketOverfull()
    {
        var fixture = OverfullBucket(baselineCount: (L + 2), currentCount: (L + 1));
        var deletedPath = OverfullMemberPath((L + 1));
        var changes = RawChangeSet.CreateWithKinds(
            [(deletedPath, RawChangeKind.Deleted)]);

        Assert.Contains(deletedPath, fixture.Baseline.Keys);
        Assert.DoesNotContain(deletedPath, fixture.Files.Keys);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;
        AssertNonGrowingBucketIsObserved(diagnostics, (L + 1));
    }

    [Fact]
    public void Sl003StillRefusesAnAdditionToAnOverfullBucket()
    {
        var fixture = OverfullBucket(baselineCount: (L + 1), currentCount: (L + 2));
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath((L + 1)), RawChangeKind.Added)]);
        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build(changes))
                .Diagnostics,
            item => item.Path == OverfullBucketPath);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(
            $"directory contains {L + 2} files (admission limit {RepositoryRules.DirectoryFileLimit}, "
            + $"repository tolerance {RepositoryRules.DirectoryToleranceLimit}; "
            + "split per CLAUDE.md 8)",
            diagnostic.Message);
    }

    [Fact]
    public void Sl003RefusesSameDirectoryRenameBecauseRawChangesDoNotProveIdentity()
    {
        var fixture = OverfullBucket(baselineCount: (L + 1), currentCount: (L + 1));
        var oldPath = OverfullMemberPath(L);
        var renamedPath = $"{OverfullBucketPath}/RenamedMember.scribe.cs";
        fixture.Files.Remove(oldPath);
        fixture.Files[renamedPath] = "-- renamed member\n";
        var changes = RawChangeSet.CreateWithKinds(
        [
            (oldPath, RawChangeKind.Deleted),
            (renamedPath, RawChangeKind.Added),
        ]);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;
        // RawChangeSet has no provable rename identity. Treating Deleted(old)+Added(new)
        // as non-growing would break union closure, so the new capacity path must block.
        AssertOverfullBucketIsBlocked(diagnostics, (L + 1));
    }

    [Fact]
    public void Sl003ObservesACopySourceInAnOverfullBucketWithoutBlocking()
    {
        var fixture = OverfullBucket(baselineCount: (L + 1), currentCount: (L + 1));
        var sourcePath = OverfullMemberPath(0);
        const string copyPath = "D5/S0/CopyTarget/Member00Copy.lean";
        fixture.Files[copyPath] = "-- copied member\n";
        fixture.Reports[copyPath] = EmptyLeanReport();
        var changes = RawChangeSet.CreateWithKinds(
        [
            (sourcePath, RawChangeKind.Copied),
            (copyPath, RawChangeKind.Added),
        ]);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;
        AssertNonGrowingBucketIsObserved(diagnostics, (L + 1));
    }

    [Fact]
    public void Sl003RefusesDeleteAddAtToleranceBecauseTheNewPathBreaksUnionClosure()
    {
        var count = RepositoryRules.DirectoryToleranceLimit;
        var fixture = OverfullBucket(baselineCount: count, currentCount: count);
        var deletedPath = OverfullMemberPath(0);
        var addedPath = $"{OverfullBucketPath}/BranchA.scribe.cs";
        fixture.Files.Remove(deletedPath);
        fixture.Files[addedPath] = "// branch A\n";
        var changes = RawChangeSet.CreateWithKinds(
        [
            (deletedPath, RawChangeKind.Deleted),
            (addedPath, RawChangeKind.Added),
        ]);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;
        // A second branch can delete the same old path and add BranchB. Each branch still
        // has the tolerance-sized path set, but their union has one more path, so cardinality
        // equality is not sufficient.
        AssertOverfullBucketIsBlocked(diagnostics, count);
    }

    [Fact]
    public void Sl003ObservesEachNonGrowingBranchInsideTheToleranceBand()
    {
        var first = OverfullBucket(baselineCount: (L + 1), currentCount: (L + 1));
        var second = OverfullBucket(baselineCount: (L + 1), currentCount: (L + 1));
        var firstDiagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            first.Build(RawChangeSet.CreateWithKinds(
                [(OverfullMemberPath(0), RawChangeKind.Modified)]))).Diagnostics;
        var secondDiagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            second.Build(RawChangeSet.CreateWithKinds(
                [(OverfullMemberPath(1), RawChangeKind.Modified)]))).Diagnostics;
        AssertNonGrowingBucketIsObserved(firstDiagnostics, (L + 1));
        AssertNonGrowingBucketIsObserved(secondDiagnostics, (L + 1));
    }

    [Fact]
    public void Sl003AdmitsCandidateAtDirectoryLimit()
    {
        var fixture = OverfullBucket(baselineCount: (L - 1), currentCount: L);
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath((L - 1)), RawChangeKind.Added)]);

        var context = fixture.Build(changes);
        Assert.Equal((L - 1), CapacityPathCount(context.Baseline));
        Assert.Equal(L, CapacityPathCount(context.Current));
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3), context).Diagnostics;
        // The admission limit is the boundary, so reaching it remains admitted.
        Assert.DoesNotContain(diagnostics, item => item.Path == OverfullBucketPath);
    }

    [Fact]
    public void Sl003BlocksPathGrowthRelativeToBaselineForAnOverfullCandidate()
    {
        var fixture = OverfullBucket(baselineCount: (L + 1), currentCount: (L + 1));
        fixture.Baseline.Remove(OverfullMemberPath(L));
        fixture.Baseline[$"{OverfullBucketPath}/DevOnly.scribe.cs"] = "// dev-only member\n";
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(0), RawChangeKind.Modified)]);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;
        AssertOverfullBucketIsBlocked(diagnostics, (L + 1));
    }

    [Fact]
    public void Sl003ExcludesBlueprintProjectionPathsFromBaselineCapacityMembership()
    {
        var fixture = OverfullBucket(baselineCount: (L + 1), currentCount: (L + 1));
        var context = fixture.Build(RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(0), RawChangeKind.Modified)]));
        var baselinePaths = RepositoryRules.CapacityPathsByDirectory(
            context.Baseline.Files.Keys);
        Assert.Equal((L + 1), baselinePaths[OverfullBucketPath].Count);
        Assert.DoesNotContain(OverfullExcludedPath, baselinePaths[OverfullBucketPath]);
    }

    [Fact]
    public void Sl003LeavesAnOverfullBucketAloneWhenTheChangeDoesNotTouchIt()
    {
        var fixture = OverfullBucket(baselineCount: (L + 1), currentCount: (L + 1));
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;
        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.Path == OverfullBucketPath);
    }

    [Fact]
    public void Sl003CurrentBlocksUntouchedBucketBeyondRepositoryTolerance()
    {
        var count = RepositoryRules.DirectoryToleranceLimit + 1;
        var fixture = OverfullBucket(baselineCount: count, currentCount: count);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;

        Assert.Contains(diagnostics, diagnostic =>
            diagnostic.Path == OverfullBucketPath
            && diagnostic.AdmissionEffect == AdmissionEffect.Block);
    }

    [Fact]
    public void Sl003RefusesFirstCapacityCountedPathPastAdmissionLimit()
    {
        var fixture = OverfullBucket(
            baselineCount: RepositoryRules.DirectoryFileLimit,
            currentCount: RepositoryRules.DirectoryFileLimit + 1);
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(RepositoryRules.DirectoryFileLimit), RawChangeKind.Added)]);

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;

        Assert.Contains(diagnostics, diagnostic =>
            diagnostic.Path == OverfullBucketPath
            && diagnostic.AdmissionEffect == AdmissionEffect.Block);
    }

    [Fact]
    public void Sl003RefusesNewPathEvenWhenBucketAlreadyExceedsRepositoryTolerance()
    {
        var fixture = OverfullBucket(
            baselineCount: RepositoryRules.DirectoryToleranceLimit + 1,
            currentCount: RepositoryRules.DirectoryToleranceLimit + 2);
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(RepositoryRules.DirectoryToleranceLimit + 1), RawChangeKind.Added)]);

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;

        Assert.Contains(diagnostics, diagnostic =>
            diagnostic.Path == OverfullBucketPath
            && diagnostic.AdmissionEffect == AdmissionEffect.Block);
    }

    private const string OverfullBucketPath = "Blueprint/D5/S0/Overfull";

    private const string OverfullExcludedPath = $"{OverfullBucketPath}/Projection.md";

    private static RuleFixture OverfullBucket(int baselineCount, int currentCount)
    {
        var fixture = new RuleFixture();
        fixture.Files[OverfullExcludedPath] = "# projection\n";
        fixture.Baseline[OverfullExcludedPath] = "# projection\n";
        for (var index = 0; index < baselineCount; index++)
        {
            var path = OverfullMemberPath(index);
            fixture.Baseline[path] = "-- member\n";
        }

        for (var index = 0; index < currentCount; index++)
        {
            var path = OverfullMemberPath(index);
            fixture.Files[path] = "-- member\n";
        }

        return fixture;
    }

    private static string OverfullMemberPath(int index) =>
        $"{OverfullBucketPath}/Member{index:00}.scribe.cs";

    private static int CapacityPathCount(RepositorySnapshot snapshot) =>
        RepositoryRules.CapacityPathsByDirectory(snapshot.Files.Keys)
            .GetValueOrDefault(OverfullBucketPath)?.Count ?? 0;

    private static LeanFileReport EmptyLeanReport() =>
        new(ImmutableArray<string>.Empty, ImmutableArray<LeanDeclaration>.Empty);

    private static void AssertNonGrowingBucketIsObserved(
        ImmutableArray<Diagnostic> diagnostics,
        int currentCount)
    {
        var diagnostic = Assert.Single(diagnostics, item => item.Path == OverfullBucketPath);
        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.Equal(
            $"directory is overfull at {currentCount} files (admission limit "
            + $"{RepositoryRules.DirectoryFileLimit}, repository tolerance "
            + $"{RepositoryRules.DirectoryToleranceLimit}), but this change introduced no "
            + "capacity-counted path absent from the protected baseline; split per CLAUDE.md 8",
            diagnostic.Message);
    }

    private static void AssertOverfullBucketIsBlocked(
        ImmutableArray<Diagnostic> diagnostics,
        int currentCount)
    {
        var diagnostic = Assert.Single(diagnostics, item => item.Path == OverfullBucketPath);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(
            $"directory contains {currentCount} files (admission limit "
            + $"{RepositoryRules.DirectoryFileLimit}, repository tolerance "
            + $"{RepositoryRules.DirectoryToleranceLimit}; split per CLAUDE.md 8)",
            diagnostic.Message);
    }
    [Fact]
    public void Sl003CurrentBlocksAnAlreadyOversizeArtifact()
    {
        var fixture = new RuleFixture();
        var oversize = fixture.Files[RuleFixture.RingPath]
            + string.Concat(Enumerable.Repeat("-- pad\n", 801));
        fixture.Files[RuleFixture.RingPath] = oversize;
        fixture.Baseline[RuleFixture.RingPath] = oversize;

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build()).Diagnostics);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("exceeds 800 lines", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl003BlocksTheCandidateThatGrewAnAlreadyOversizeArtifact()
    {
        var fixture = new RuleFixture();
        var baselineOversize = fixture.Files[RuleFixture.RingPath]
            + string.Concat(Enumerable.Repeat("-- pad\n", 801));
        fixture.Files[RuleFixture.RingPath] = baselineOversize + "-- one more line\n";
        fixture.Baseline[RuleFixture.RingPath] = baselineOversize;

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build()).Diagnostics);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal("artifact exceeds 800 lines", diagnostic.Message);
    }

    // Baseline absence means this change created the file, so the artifact grew and blocks.
    [Fact]
    public void Sl003BlocksAnOversizeArtifactThisChangeCreated()
    {
        var fixture = new RuleFixture();
        fixture.Files["Meta/NewOversize.txt"] =
            string.Concat(Enumerable.Repeat("pad\n", 801));
        fixture.Changes.Add("Meta/NewOversize.txt");

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build()).Diagnostics,
            item => item.Path == "Meta/NewOversize.txt");
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

}
