using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleEngineCapacityTests
{
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
            fixture.ForkPoint[path] = "fixture\n";
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
        for (var index = 0; index < 13; index++)
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
        for (var index = 0; index < 13; index++)
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
    public void Sl003RefusesNetGrowthOfAnOverfullBucket()
    {
        var fixture = OverfullBucket(forkPointCount: 11, currentCount: 13);
        var changes = RawChangeSet.CreateWithKinds(
        [
            (OverfullMemberPath(11), RawChangeKind.Added),
            (OverfullMemberPath(12), RawChangeKind.Added),
        ]);
        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build(changes)).Diagnostics,
            item => item.Path == OverfullBucketPath);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(
            $"directory contains 13 files (admission limit {RepositoryRules.DirectoryFileLimit}, "
            + $"repository tolerance {RepositoryRules.DirectoryToleranceLimit}; "
            + "split per CLAUDE.md 8)",
            diagnostic.Message);
    }

    [Fact]
    public void Sl003RefusesNewOverfullBucketAbsentFromForkPoint()
    {
        var fixture = OverfullBucket(forkPointCount: 0, currentCount: 13);
        var changes = RawChangeSet.CreateWithKinds(
            Enumerable.Range(0, 13)
                .Select(static index => (OverfullMemberPath(index), RawChangeKind.Added)));
        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build(changes)).Diagnostics,
            item => item.Path == OverfullBucketPath);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    [Fact]
    public void Sl003ObservesAModificationInsideAnOverfullBucket()
    {
        var fixture = OverfullBucket(forkPointCount: 13, currentCount: 13);
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(0), RawChangeKind.Modified)]);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;
        AssertNonGrowingBucketIsObserved(diagnostics, 13);
    }

    [Fact]
    public void Sl003ObservesADeletionThatLeavesTheBucketOverfull()
    {
        var fixture = OverfullBucket(forkPointCount: 14, currentCount: 13);
        var deletedPath = OverfullMemberPath(13);
        var changes = RawChangeSet.CreateWithKinds(
            [(deletedPath, RawChangeKind.Deleted)]);

        Assert.Contains(deletedPath, fixture.ForkPoint.Keys);
        Assert.DoesNotContain(deletedPath, fixture.Files.Keys);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;
        AssertNonGrowingBucketIsObserved(diagnostics, 13);
    }

    [Fact]
    public void Sl003StillRefusesAnAdditionToAnOverfullBucket()
    {
        var fixture = OverfullBucket(forkPointCount: 13, currentCount: 14);
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(13), RawChangeKind.Added)]);
        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build(changes))
                .Diagnostics,
            item => item.Path == OverfullBucketPath);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(
            $"directory contains 14 files (admission limit {RepositoryRules.DirectoryFileLimit}, "
            + $"repository tolerance {RepositoryRules.DirectoryToleranceLimit}; "
            + "split per CLAUDE.md 8)",
            diagnostic.Message);
    }

    [Fact]
    public void Sl003RefusesSameDirectoryRenameBecauseRawChangesDoNotProveIdentity()
    {
        var fixture = OverfullBucket(forkPointCount: 13, currentCount: 13);
        var oldPath = OverfullMemberPath(12);
        var renamedPath = $"{OverfullBucketPath}/Renamed12.scribe.cs";
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
        AssertOverfullBucketIsBlocked(diagnostics, 13);
    }

    [Fact]
    public void Sl003ObservesACopySourceInAnOverfullBucketWithoutBlocking()
    {
        var fixture = OverfullBucket(forkPointCount: 13, currentCount: 13);
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
        AssertNonGrowingBucketIsObserved(diagnostics, 13);
    }

    [Fact]
    public void Sl003RefusesDeleteAddAtToleranceBecauseTheNewPathBreaksUnionClosure()
    {
        var count = RepositoryRules.DirectoryToleranceLimit;
        var fixture = OverfullBucket(forkPointCount: count, currentCount: count);
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
        // has 24 paths, but their union has 25, so cardinality equality is not sufficient.
        AssertOverfullBucketIsBlocked(diagnostics, count);
    }

    [Fact]
    public void Sl003ObservesEachNonGrowingBranchInsideTheToleranceBand()
    {
        var first = OverfullBucket(forkPointCount: 13, currentCount: 13);
        var second = OverfullBucket(forkPointCount: 13, currentCount: 13);
        var firstDiagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            first.Build(RawChangeSet.CreateWithKinds(
                [(OverfullMemberPath(0), RawChangeKind.Modified)]))).Diagnostics;
        var secondDiagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            second.Build(RawChangeSet.CreateWithKinds(
                [(OverfullMemberPath(1), RawChangeKind.Modified)]))).Diagnostics;
        AssertNonGrowingBucketIsObserved(firstDiagnostics, 13);
        AssertNonGrowingBucketIsObserved(secondDiagnostics, 13);
    }

    [Fact]
    public void Sl003AdmitsTwelveFileCandidateAfterBaselineAdvancesFromItsElevenFileForkPoint()
    {
        var fixture = OverfullBucket(forkPointCount: 11, currentCount: 12);
        fixture.Baseline[OverfullMemberPath(11)] = "// dev member 11\n";
        fixture.Baseline[OverfullMemberPath(12)] = "// dev member 12\n";
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(11), RawChangeKind.Added)]);

        var context = fixture.Build(changes);
        Assert.Equal(11, CapacityPathCount(context.ForkPoint));
        Assert.Equal(13, CapacityPathCount(context.Baseline));
        Assert.Equal(12, CapacityPathCount(context.Current));
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3), context).Diagnostics;
        // Twelve is the admission boundary, so this in-flight candidate remains admitted
        // even after dev advances beyond it.
        Assert.DoesNotContain(diagnostics, item => item.Path == OverfullBucketPath);
    }

    [Fact]
    public void Sl003UsesForkPointPathsInsteadOfTheMovingBaselineForAnOverfullCandidate()
    {
        var fixture = OverfullBucket(forkPointCount: 13, currentCount: 13);
        fixture.Baseline.Remove(OverfullMemberPath(12));
        fixture.Baseline[$"{OverfullBucketPath}/DevOnly.scribe.cs"] = "// dev-only member\n";
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(0), RawChangeKind.Modified)]);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;
        // Current is a subset of its own ForkPoint but not of the independently moving
        // Baseline. Replacing ForkPoint with Baseline must turn this assertion red.
        AssertNonGrowingBucketIsObserved(diagnostics, 13);
    }

    [Fact]
    public void Sl003ExcludesBlueprintProjectionPathsFromForkPointCapacityMembership()
    {
        var fixture = OverfullBucket(forkPointCount: 13, currentCount: 13);
        var context = fixture.Build(RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(0), RawChangeKind.Modified)]));
        var forkPointPaths = RepositoryRules.CapacityPathsByDirectory(
            context.ForkPoint.Files.Keys);
        Assert.Equal(13, forkPointPaths[OverfullBucketPath].Count);
        Assert.DoesNotContain(OverfullExcludedPath, forkPointPaths[OverfullBucketPath]);
    }

    [Fact]
    public void Sl003LeavesAnOverfullBucketAloneWhenTheChangeDoesNotTouchIt()
    {
        var fixture = OverfullBucket(forkPointCount: 13, currentCount: 13);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;
        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.Path == OverfullBucketPath);
    }

    [Fact]
    public void Sl003DoesNotBlockUntouchedBucketBeyondRepositoryTolerance()
    {
        var count = RepositoryRules.DirectoryToleranceLimit + 1;
        var fixture = OverfullBucket(forkPointCount: count, currentCount: count);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;

        Assert.DoesNotContain(diagnostics, diagnostic =>
            diagnostic.Path == OverfullBucketPath
            && diagnostic.AdmissionEffect == AdmissionEffect.Block);
    }

    [Fact]
    public void Sl003RefusesThirteenthCapacityCountedPath()
    {
        var fixture = OverfullBucket(forkPointCount: 12, currentCount: 13);
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(12), RawChangeKind.Added)]);

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
        var fixture = OverfullBucket(forkPointCount: 25, currentCount: 26);
        var changes = RawChangeSet.CreateWithKinds(
            [(OverfullMemberPath(25), RawChangeKind.Added)]);

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build(changes)).Diagnostics;

        Assert.Contains(diagnostics, diagnostic =>
            diagnostic.Path == OverfullBucketPath
            && diagnostic.AdmissionEffect == AdmissionEffect.Block);
    }

    [Fact]
    public void Sl003DoesNotChargeCandidateForUnknownDebtAlreadyPresentAtItsForkPoint()
    {
        var methods = UnknownMethodNames(281);
        var fixture = UnknownDebtFixture(
            current: [("Synthetic.Tests", methods)],
            forkPoint: [("Synthetic.Tests", methods)]);

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3),
            fixture.Build()).Diagnostics;

        AssertNoBlockingUnknownDebt(diagnostics);
    }

    [Fact]
    public void Sl003BlocksAndNamesTheUnknownMethodIntroducedByTheCandidate()
    {
        var forkMethods = UnknownMethodNames(280);
        var currentMethods = forkMethods.Append("Debt280").ToArray();
        var fixture = UnknownDebtFixture(
            current: [("Synthetic.Tests", currentMethods)],
            forkPoint: [("Synthetic.Tests", forkMethods)]);

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build()).Diagnostics,
            static item => item.Message.Contains("unknown test method", StringComparison.Ordinal));

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("DebtTests.Debt280", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl003ToleratesTheUnionOfTwoIndividuallyCompliantUnknownDebtSets()
    {
        var firstMethods = UnknownMethodNames(280);
        var secondMethods = UnknownMethodNames(281).Skip(1).ToArray();
        var unionMethods = firstMethods.Union(secondMethods, StringComparer.Ordinal).ToArray();
        var first = UnknownDebtFixture(
            current: [("Synthetic.Tests", firstMethods)],
            forkPoint: [("Synthetic.Tests", firstMethods)]);
        var second = UnknownDebtFixture(
            current: [("Synthetic.Tests", secondMethods)],
            forkPoint: [("Synthetic.Tests", secondMethods)]);
        var union = UnknownDebtFixture(
            current: [("Synthetic.Tests", unionMethods)],
            forkPoint: [("Synthetic.Tests", unionMethods)]);

        AssertNoBlockingUnknownDebt(RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3), first.Build()).Diagnostics);
        AssertNoBlockingUnknownDebt(RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3), second.Build()).Diagnostics);
        Assert.Equal(281, unionMethods.Length);
        AssertNoBlockingUnknownDebt(RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(3), union.Build()).Diagnostics);
    }

    [Fact]
    public void Sl003RejectsRepositoryUnknownDebtPastTheToleranceBand()
    {
        var methods = UnknownMethodNames(282);
        var fixture = UnknownDebtFixture(
            current: [("Synthetic.Tests", methods)],
            forkPoint: [("Synthetic.Tests", methods)]);

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build()).Diagnostics,
            static item => item.Message.Contains("repository tolerance", StringComparison.Ordinal)
                && item.Message.Contains("unknown test methods", StringComparison.Ordinal));

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("282", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl003TreatsAnUnknownMethodRenameAsNewDebt()
    {
        var fixture = UnknownDebtFixture(
            current: [("Synthetic.Tests", ["RenamedDebt"])],
            forkPoint: [("Synthetic.Tests", ["OriginalDebt"])]);

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build()).Diagnostics,
            static item => item.Message.Contains("unknown test method", StringComparison.Ordinal));

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("DebtTests.RenamedDebt", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl003TreatsAnUnknownMethodMoveAcrossProjectPartitionsAsNewDebt()
    {
        var fixture = UnknownDebtFixture(
            current: [("Beta.Tests", ["MovedDebt"])],
            forkPoint: [("Alpha.Tests", ["MovedDebt"])]);

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build()).Diagnostics,
            static item => item.Message.Contains("unknown test method", StringComparison.Ordinal));

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("tools/tests/Beta.Tests", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("DebtTests.MovedDebt", diagnostic.Message, StringComparison.Ordinal);
    }

    private const string OverfullBucketPath = "Blueprint/D5/S0/Overfull";

    private const string OverfullExcludedPath = $"{OverfullBucketPath}/Projection.md";

    private static RuleFixture OverfullBucket(int forkPointCount, int currentCount)
    {
        var fixture = new RuleFixture();
        fixture.Files[OverfullExcludedPath] = "# projection\n";
        fixture.Baseline[OverfullExcludedPath] = "# projection\n";
        fixture.ForkPoint[OverfullExcludedPath] = "# projection\n";
        for (var index = 0; index < forkPointCount; index++)
        {
            var path = OverfullMemberPath(index);
            fixture.Baseline[path] = "-- member\n";
            fixture.ForkPoint[path] = "-- member\n";
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

    private static RuleFixture UnknownDebtFixture(
        IReadOnlyList<(string Partition, IReadOnlyList<string> Methods)> current,
        IReadOnlyList<(string Partition, IReadOnlyList<string> Methods)> forkPoint)
    {
        var fixture = new RuleFixture();
        foreach (var (partition, methods) in current)
        {
            AddUnknownDebtPartition(fixture.Files, partition, methods);
            AddUnknownDebtPartition(fixture.Baseline, partition, methods);
        }

        foreach (var (partition, methods) in forkPoint)
        {
            AddUnknownDebtPartition(fixture.ForkPoint, partition, methods);
        }

        return fixture;
    }

    private static void AddUnknownDebtPartition(
        IDictionary<string, string> files,
        string partition,
        IReadOnlyList<string> methods)
    {
        var root = $"tools/tests/{partition}";
        files[$"{root}/{partition}.csproj"] =
            "<Project Sdk=\"Microsoft.NET.Sdk\"><ItemGroup>"
            + "<PackageReference Include=\"xunit\" /></ItemGroup></Project>\n";
        files[$"{root}/DebtTests.cs"] = "class DebtTests\n{\n"
            + string.Join('\n', methods.Select(static method =>
                $"[Fact] public void {method}() {{ var path = GetPath(); File.ReadAllText(path); }}"))
            + "\n}\n";
    }

    private static string[] UnknownMethodNames(int count) => Enumerable.Range(0, count)
        .Select(static index => $"Debt{index:000}")
        .ToArray();

    private static void AssertNoBlockingUnknownDebt(ImmutableArray<Diagnostic> diagnostics) =>
        Assert.DoesNotContain(diagnostics, static item =>
            item.AdmissionEffect == AdmissionEffect.Block
            && item.Message.Contains("unknown test method", StringComparison.Ordinal));

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
            + "capacity-counted path absent from its fork point; split per CLAUDE.md 8",
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
    // 2026-08-15 实测的连坐:dev 上 DigestionLedgerAligner.cs 因两个 PR 的**并集**达到 823 行
    // (各自树内是 799 与 639,都没越线,各自 admit 都是对的)。此后每一个 PR 的准入都判红,
    // 包括 #1890/#1891/#1896/#1897 这些从未碰过该文件的——全仓锁死约一小时。
    //
    // 阻断该落在把它推过线的那个候选身上,不该落在无辜候选身上。判据取自分叉点:本次改动
    // 有没有让它变长。这与目录轴既有的做法同构(带内候选只有引入了分叉点上不存在的路径才阻断,
    // 见 RepositoryRules.Structure.cs 的 DirectoryToleranceLimit 注释与 2026-08-13 判例)。
    //
    // 检测不降级:超线仍然出 finding,只是无辜者那条是 Observe;全仓检测由 push
    // 侧的 capacity-audit 承担。
    [Fact]
    public void Sl003DoesNotBlockACandidateThatDidNotGrowAnAlreadyOversizeArtifact()
    {
        var fixture = new RuleFixture();
        var oversize = fixture.Files[RuleFixture.RingPath]
            + string.Concat(Enumerable.Repeat("-- pad\n", 801));
        fixture.Files[RuleFixture.RingPath] = oversize;
        fixture.Baseline[RuleFixture.RingPath] = oversize;
        fixture.ForkPoint[RuleFixture.RingPath] = oversize;

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build()).Diagnostics);
        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.Contains("did not grow it", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void Sl003BlocksTheCandidateThatGrewAnAlreadyOversizeArtifact()
    {
        var fixture = new RuleFixture();
        var forkOversize = fixture.Files[RuleFixture.RingPath]
            + string.Concat(Enumerable.Repeat("-- pad\n", 801));
        fixture.Files[RuleFixture.RingPath] = forkOversize + "-- one more line\n";
        fixture.Baseline[RuleFixture.RingPath] = forkOversize;
        fixture.ForkPoint[RuleFixture.RingPath] = forkOversize;

        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build()).Diagnostics);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal("artifact exceeds 800 lines", diagnostic.Message);
    }

    // 分叉点上没有这个文件 = 本次改动新建了它,那它当然是"长出来的",阻断。
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
