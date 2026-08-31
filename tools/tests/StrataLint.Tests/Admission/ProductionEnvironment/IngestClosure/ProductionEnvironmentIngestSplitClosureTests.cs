using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void IngestReportFreeAcceptsPlannerClauseChainForNewUncoveredClaim()
    {
        const string oldText = "# PZG\n\n**定理 1.1(A)**。old claim。\n";
        const string currentText = oldText
            + "\n**定理 1.2(B)**。new claim。\n"
            + "\n**(i)** first clause。\n"
            + "\n**(ii)** second clause。\n";
        var fixture = new RuleFixture();
        var oldAtom = Assert.Single(PzgAtomizer.Atomize(
            Encoding.UTF8.GetBytes(oldText),
            DigestionTestSupport.Rules).Claims);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = currentText;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = oldText;
        InstallProjectedLedger(fixture, IngestLedger(AtomizerRegistry.PzgId, oldAtom), oldAtom);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var reportSource = new FakeLeanReportSource(report: null);
        var scribeVerifier = new FakeScribeEmissionVerifier(verification: null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            scribeVerifier);

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);
        var entries = BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries();
        var parent = Assert.Single(entries, static entry => entry.Receipts.ChainAtoms.Length > 0);
        Assert.Empty(parent.CoverageGids);
        Assert.Equal(3, parent.Receipts.ChainAtoms.Length);
        Assert.All(parent.Receipts.ChainAtoms, childId =>
            Assert.Contains(entries, entry => entry.AtomId == childId));

        var generated = DirectoryLedgerTestSupport.OverlayRepositoryFiles(
            temporary,
            fixture.Files);
        var fixedPointReportSource = new FakeLeanReportSource(report: null);
        var fixedPointScribeVerifier = new FakeScribeEmissionVerifier(verification: null);
        var fixedPointEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(generated),
                Snapshot(fixture.Baseline)),
            fixedPointReportSource,
            fixedPointScribeVerifier);

        var fixedPointResult = fixedPointEnvironment.Ingest(ReportInputUnchangedArguments);

        Assert.True(fixedPointResult.Success, fixedPointResult.Error);
        Assert.Contains("ledger_changed=false", fixedPointResult.Output, StringComparison.Ordinal);
        Assert.Equal(0, fixedPointReportSource.CallCount);
        Assert.Equal(0, fixedPointScribeVerifier.CallCount);
    }

    [Fact]
    public void IngestReportFreeAcceptsPureAdditionBesideSeenCoveredEntryWithoutRewritingIt()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        const string oldText = "# Synthetic\n\n**定理 1.1(A)**。old。\n\n";
        const string currentText = oldText + "**定理 1.2(B)**。new。\n";
        var fixture = new RuleFixture();
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(
            SyntheticNumberedAtomizer.Id,
            Encoding.UTF8.GetBytes(oldText),
            DigestionTestSupport.Rules).Claims);
        var currentOldAtom = Assert.Single(AtomizerRegistry.Atomize(
            SyntheticNumberedAtomizer.Id,
            Encoding.UTF8.GetBytes(currentText),
            DigestionTestSupport.Rules).Claims,
            atom => atom.Fingerprints.RawSha256 == oldAtom.Fingerprints.RawSha256);
        Assert.Equal(oldAtom.Fingerprints.RawSha256, currentOldAtom.Fingerprints.RawSha256);
        Assert.Equal(oldAtom.StartByte, currentOldAtom.StartByte);
        Assert.Equal(oldAtom.EndByte, currentOldAtom.EndByte);
        Assert.Equal(oldAtom.RawBytes.ToArray(), currentOldAtom.RawBytes.ToArray());
        Assert.Equal(oldAtom.Fingerprints, currentOldAtom.Fingerprints);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = currentText;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = oldText;
        InstallProjectedLedger(
            fixture,
            IngestLedger(SyntheticNumberedAtomizer.Id, oldAtom),
            oldAtom);
        var coveredPath = DirectoryAtomPath(AtomId(oldAtom), "residual-open");
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[coveredPath] = files[coveredPath].Replace(
                "coverage_gids: []",
                $"coverage_gids:\n  - {coverageGid}",
                StringComparison.Ordinal);
        }

        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var coveredOutputPath = Path.Combine(
            temporary.Path,
            coveredPath.Replace('/', Path.DirectorySeparatorChar));
        var unchangedWriteTime = new DateTime(2000, 1, 1, 0, 0, 0, DateTimeKind.Utc);
        File.SetLastWriteTimeUtc(coveredOutputPath, unchangedWriteTime);
        var coveredEntryImage = coveredPath + "\0"
            + Convert.ToBase64String(Encoding.UTF8.GetBytes(fixture.Files[coveredPath]))
            + "\n";
        var before = GeneratedIngestImage(temporary);
        Assert.Contains(coveredEntryImage, before, StringComparison.Ordinal);
        var reportSource = new FakeLeanReportSource(report: null);
        var scribeVerifier = new FakeScribeEmissionVerifier(verification: null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            scribeVerifier);

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);
        Assert.Contains(coveredEntryImage, GeneratedIngestImage(temporary), StringComparison.Ordinal);
        Assert.Equal(unchangedWriteTime, File.GetLastWriteTimeUtc(coveredOutputPath));
    }

    [Fact]
    public void IngestReportFreeExcludesPlannerSourceMetadataWriteFromCoveredEntryAuthorityEvidence()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        const string oldText = "# Synthetic\n\n**定理 1.1(A)**。covered。\n\n"
            + "**定理 1.2(B)**。trailing。";
        const string currentText = oldText
            + " appended context。\n\n**定理 1.3(C)**。new。\n";
        var fixture = new RuleFixture();
        var oldAtoms = AtomizerRegistry.Atomize(
            SyntheticNumberedAtomizer.Id,
            Encoding.UTF8.GetBytes(oldText),
            DigestionTestSupport.Rules).Claims;
        var currentAtoms = AtomizerRegistry.Atomize(
            SyntheticNumberedAtomizer.Id,
            Encoding.UTF8.GetBytes(currentText),
            DigestionTestSupport.Rules).Claims;
        Assert.Equal(2, oldAtoms.Length);
        Assert.Equal(3, currentAtoms.Length);
        var coveredAtom = oldAtoms[0];
        var staleAtom = oldAtoms[1];
        var currentCoveredAtom = currentAtoms[0];
        var currentTrailingAtom = currentAtoms[1];
        Assert.Equal(coveredAtom.RawBytes.ToArray(), currentCoveredAtom.RawBytes.ToArray());
        Assert.NotEqual(staleAtom.Fingerprints.RawSha256, currentTrailingAtom.Fingerprints.RawSha256);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = currentText;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = oldText;
        var ledger = DigestionTestSupport.Document(
            SyntheticNumberedAtomizer.Id,
            [
                DigestionTestSupport.Entry(
                    coveredAtom,
                    AtomId(coveredAtom),
                    SyntheticNumberedAtomizer.Id,
                    coverageGids: [coverageGid],
                    sourceId: "fixture-source",
                    sourcePath: RuleFixture.FixtureDigestionSourcePath),
                DigestionTestSupport.Entry(
                    staleAtom,
                    AtomId(staleAtom),
                    SyntheticNumberedAtomizer.Id,
                    sourceId: "fixture-source",
                    sourcePath: RuleFixture.FixtureDigestionSourcePath),
            ],
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            GenreRegistryCheck.Collected([]));
        InstallProjectedLedger(
            fixture,
            ledger,
            existingAtom: null);
        foreach (var atom in oldAtoms)
        {
            var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
            var text = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
            fixture.Files[captured.RelativePath] = text;
            fixture.Baseline[captured.RelativePath] = text;
        }

        var coveredPath = DirectoryAtomPath(AtomId(coveredAtom), "residual-open");
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var coveredOutputPath = Path.Combine(
            temporary.Path,
            coveredPath.Replace('/', Path.DirectorySeparatorChar));
        var unchangedWriteTime = new DateTime(2000, 1, 1, 0, 0, 0, DateTimeKind.Utc);
        File.SetLastWriteTimeUtc(coveredOutputPath, unchangedWriteTime);
        var coveredEntryImage = coveredPath + "\0"
            + Convert.ToBase64String(Encoding.UTF8.GetBytes(fixture.Files[coveredPath]))
            + "\n";
        var reportSource = new FakeLeanReportSource(report: null);
        var scribeVerifier = new FakeScribeEmissionVerifier(verification: null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            scribeVerifier);

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);
        Assert.Contains(coveredEntryImage, GeneratedIngestImage(temporary), StringComparison.Ordinal);
        Assert.Equal(unchangedWriteTime, File.GetLastWriteTimeUtc(coveredOutputPath));
        var source = Assert.Single(BackfillInventoryLoader.LoadRoot(temporary.Path)
            .RequireDigestionSources());
        Assert.Empty(source.AcknowledgedStale);
    }

    [Theory]
    [InlineData(false, "covered entry closure-entry disappeared from plan")]
    [InlineData(true, "covered entry closure-entry coverage was cleared in plan")]
    public void ClassifyPlannedIdentifiesCoveredEntryLoss(bool retainEntry, string expectedWitness)
    {
        var entry = StatusAuthorityClosureEntry();
        var current = DigestionTestSupport.Document(
            entry.Atomizer,
            [entry],
            sourceId: entry.SourceId,
            sourcePath: entry.SourcePath);
        var source = Assert.Single(current.RequireDigestionSources());
        var planned = current.WithDigestionSources([
            source with
            {
                Entries = retainEntry ? [entry with { CoverageGids = [] }] : [],
            },
        ]);
        var alignment = new DigestionLedgerAlignment(
            ImmutableDictionary.CreateRange(StringComparer.Ordinal,
            [
                KeyValuePair.Create(entry.AtomId, DigestionReceiptAlignment.Seen),
            ]),
            ImmutableDictionary<string, DigestionAtom>.Empty,
            ImmutableDictionary<string, ImmutableHashSet<string>>.Empty,
            ImmutableDictionary<string, GenreRegistryCheck>.Empty,
            [],
            [],
            ImmutableHashSet<string>.Empty,
            ImmutableHashSet<string>.Empty,
            [],
            [],
            []);

        var classification = IngestTruthAlignmentClassifier.ClassifyPlanned(
            current,
            current,
            planned,
            alignment,
            DigestionEvaluationScope.ChangedSet,
            RawChangeSet.Create([]));

        Assert.False(classification.IsUncoveredOnly);
        Assert.Equal(expectedWitness, classification.Witness);
    }

    [Fact]
    public void ClassifyCurrentAcceptsChainAtomReceiptsOnResidualOpenNewEntry()
    {
        var entry = StatusAuthorityClosureEntry() with
        {
            CoverageGids = [],
            Receipts = new DigestionReceipts([], [], [], ["chain-child"], null),
        };

        var classification = ClassifyCurrentOnlyNewEntry(entry);

        Assert.True(classification.IsUncoveredOnly);
        Assert.Null(classification.Witness);
    }

    [Fact]
    public void ClassifyCurrentRejectsCoverageBearingNewEntry()
    {
        var classification = ClassifyCurrentOnlyNewEntry(StatusAuthorityClosureEntry());

        Assert.False(classification.IsUncoveredOnly);
        Assert.Equal("new entry closure-entry is coverage-bearing", classification.Witness);
    }

    [Fact]
    public void ClassifyCurrentRejectsNonResidualOpenNewEntry()
    {
        var entry = StatusAuthorityClosureEntry() with
        {
            CoverageGids = [],
            Receipts = new DigestionReceipts([], [], [], [], null),
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        };

        var classification = ClassifyCurrentOnlyNewEntry(entry);

        Assert.False(classification.IsUncoveredOnly);
        Assert.Equal(
            "new entry closure-entry projected status is not residual-open",
            classification.Witness);
    }

    [Theory]
    [InlineData("entry")]
    [InlineData("source-metadata")]
    [InlineData("accepted-event")]
    [InlineData("atomizer-data")]
    [InlineData("cas")]
    [InlineData("tail")]
    [InlineData("coverage-gid")]
    [InlineData("scribe-definition")]
    [InlineData("scribe-emission")]
    public void StatusAuthorityClosureRejectsEachRetainedChangedInput(string inputKind)
    {
        var entry = StatusAuthorityClosureEntry();
        var coverageGid = Assert.Single(entry.CoverageGids);
        var documentGid = ScribeEmissionAttestation.DocumentGid(coverageGid);
        var changedPath = inputKind switch
        {
            "entry" => DirectoryAtomPath(entry.AtomId, "residual-open"),
            "source-metadata" => DirectorySourceMetadataPath(),
            "accepted-event" => FrozenLedgerChangeClassifier.AcceptedRoot + "/changed.json",
            "atomizer-data" => TheoryAtomizerDataLoader.DataPath,
            "cas" => DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..],
            "tail" => entry.Receipts.TailAuthorization!.Path,
            "coverage-gid" => "D5/S0/Carrier/Ring.lean",
            "scribe-definition" => ScribeEmissionAttestation.DefinitionPath(documentGid),
            "scribe-emission" => ScribeEmissionAttestation.EmissionPath(documentGid),
            _ => throw new ArgumentOutOfRangeException(nameof(inputKind)),
        };

        Assert.True(DigestionStatusEvaluator.StatusAuthorityClosureChanged(
            entry,
            DigestionReceiptAlignment.Seen,
            DigestionMigrationState.Residual,
            RawChangeSet.Create([changedPath]),
            isBaseFactAffected: null));
    }

    [Theory]
    [InlineData("stale")]
    [InlineData("rejected")]
    public void StatusAuthorityClosureRejectsSourcePathForEachNonSeenAlignment(
        string alignmentName)
    {
        var entry = StatusAuthorityClosureEntry();
        var alignment = alignmentName switch
        {
            "stale" => DigestionReceiptAlignment.Stale,
            "rejected" => DigestionReceiptAlignment.Rejected,
            _ => throw new ArgumentOutOfRangeException(nameof(alignmentName)),
        };

        Assert.True(DigestionStatusEvaluator.StatusAuthorityClosureChanged(
            entry,
            alignment,
            DigestionMigrationState.Residual,
            RawChangeSet.Create([entry.SourcePath]),
            isBaseFactAffected: null));
    }

    [Fact]
    public void StatusAuthorityClosureMissingAlignmentFailsClosed()
    {
        var entry = StatusAuthorityClosureEntry();
        var document = DigestionTestSupport.Document(
            entry.Atomizer,
            [entry],
            sourceId: entry.SourceId,
            sourcePath: entry.SourcePath);
        var alignment = new DigestionLedgerAlignment(
            ImmutableDictionary<string, DigestionReceiptAlignment>.Empty,
            ImmutableDictionary<string, DigestionAtom>.Empty,
            ImmutableDictionary<string, ImmutableHashSet<string>>.Empty,
            ImmutableDictionary<string, GenreRegistryCheck>.Empty,
            [],
            [],
            ImmutableHashSet<string>.Empty,
            ImmutableHashSet<string>.Empty,
            [],
            [],
            []);

        var changed = DigestionStatusEvaluator.StatusAuthorityChangedAtomIds(
            document,
            document,
            RawChangeSet.Create([entry.SourcePath]),
            alignment);

        Assert.Contains(entry.AtomId, changed);
    }

    [Fact]
    public void StatusAuthorityClosureRejectsFullScanWithoutAChangeSet()
    {
        Assert.True(DigestionStatusEvaluator.StatusAuthorityClosureChanged(
            StatusAuthorityClosureEntry(),
            DigestionReceiptAlignment.Seen,
            DigestionMigrationState.Residual,
            changes: null,
            isBaseFactAffected: null));
    }

    [Fact]
    public void StatusAuthorityClosurePropagatesChangedChainAtomToCoveredParent()
    {
        var child = StatusAuthorityClosureEntry() with
        {
            AtomId = "closure-child",
            CoverageGids = [],
            Receipts = new DigestionReceipts([], [], [], [], null),
        };
        var parent = StatusAuthorityClosureEntry() with
        {
            AtomId = "closure-parent",
            Receipts = new DigestionReceipts([], [], [], [child.AtomId], null),
        };
        var document = DigestionTestSupport.Document(
            parent.Atomizer,
            [parent, child],
            sourceId: parent.SourceId,
            sourcePath: parent.SourcePath);
        var alignment = new DigestionLedgerAlignment(
            ImmutableDictionary.CreateRange(StringComparer.Ordinal,
            [
                KeyValuePair.Create(parent.AtomId, DigestionReceiptAlignment.Seen),
                KeyValuePair.Create(child.AtomId, DigestionReceiptAlignment.Rejected),
            ]),
            ImmutableDictionary<string, DigestionAtom>.Empty,
            ImmutableDictionary<string, ImmutableHashSet<string>>.Empty,
            ImmutableDictionary<string, GenreRegistryCheck>.Empty,
            [],
            [],
            ImmutableHashSet<string>.Empty,
            ImmutableHashSet<string>.Empty,
            [],
            [],
            []);

        var changed = DigestionStatusEvaluator.StatusAuthorityChangedAtomIds(
            document,
            document,
            RawChangeSet.Create([child.SourcePath]),
            alignment);

        Assert.Contains(child.AtomId, changed);
        Assert.Contains(parent.AtomId, changed);
    }

    private static DigestionLedgerEntry StatusAuthorityClosureEntry()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        const string text = "# Synthetic\n\n**定理 1.1(A)**。old。\n";
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            SyntheticNumberedAtomizer.Id,
            Encoding.UTF8.GetBytes(text),
            DigestionTestSupport.Rules).Claims);
        return DigestionTestSupport.Entry(
            atom,
            "closure-entry",
            SyntheticNumberedAtomizer.Id,
            coverageGids: [coverageGid],
            receipts: new DigestionReceipts(
                [],
                [],
                [],
                [],
                new DigestionExternalReceipt(
                    "Evidence/tail.txt",
                    "sha256:" + new string('d', 64))),
            sourceId: "fixture-source",
            sourcePath: RuleFixture.FixtureDigestionSourcePath);
    }

    private static IngestTruthAlignmentClassification ClassifyCurrentOnlyNewEntry(
        DigestionLedgerEntry entry)
    {
        var current = DigestionTestSupport.Document(
            entry.Atomizer,
            [entry],
            sourceId: entry.SourceId,
            sourcePath: entry.SourcePath);
        var baseline = DigestionTestSupport.Document(
            entry.Atomizer,
            [],
            sourceId: entry.SourceId,
            sourcePath: entry.SourcePath);
        return IngestTruthAlignmentClassifier.ClassifyCurrent(
            LeanReportInputState.Unchanged,
            current,
            baseline);
    }
}
