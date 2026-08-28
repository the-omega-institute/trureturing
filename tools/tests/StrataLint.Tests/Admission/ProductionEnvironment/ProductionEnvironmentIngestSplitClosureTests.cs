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
        var parent = Assert.Single(entries, static entry => entry.AstPath == "theorem/1.2");
        Assert.Empty(parent.CoverageGids);
        Assert.Equal(3, parent.Receipts.ChainAtoms.Length);
        Assert.All(parent.Receipts.ChainAtoms, childId =>
            Assert.Contains(entries, entry => entry.AtomId == childId));
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
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = currentText;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = oldText;
        InstallProjectedLedger(
            fixture,
            IngestLedger(SyntheticNumberedAtomizer.Id, oldAtom),
            oldAtom);
        var coveredPath = DirectoryAtomPath("old-receipt", "residual-open");
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
        var coveredBytes = File.ReadAllBytes(coveredOutputPath);
        var unchangedWriteTime = new DateTime(2000, 1, 1, 0, 0, 0, DateTimeKind.Utc);
        File.SetLastWriteTimeUtc(coveredOutputPath, unchangedWriteTime);
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
        Assert.Equal(coveredBytes, File.ReadAllBytes(coveredOutputPath));
        Assert.Equal(unchangedWriteTime, File.GetLastWriteTimeUtc(coveredOutputPath));
    }

    [Fact]
    public void IngestReportFreeRejectsPureAdditionWhenCoveredEntryIsNoLongerSeen()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture(rewriteExistingAtom: true);
        var coveredPath = DirectoryAtomPath("old-receipt", "residual-open");
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[coveredPath] = files[coveredPath].Replace(
                "coverage_gids: []",
                $"coverage_gids:\n  - {coverageGid}",
                StringComparison.Ordinal);
        }

        AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
            "covered entry old-receipt changed status-authority inputs");
    }

    [Theory]
    [InlineData("entry")]
    [InlineData("source-metadata")]
    [InlineData("source-non-seen")]
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
            "source-non-seen" => entry.SourcePath,
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
            inputKind == "source-non-seen"
                ? DigestionReceiptAlignment.Rejected
                : DigestionReceiptAlignment.Seen,
            DigestionMigrationState.Residual,
            RawChangeSet.Create([changedPath]),
            isBaseFactAffected: null));
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
}
