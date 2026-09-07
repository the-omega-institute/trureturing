using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private static readonly string[] ReportInputUnchangedArguments =
        ["--base", "baseline"];

    [Fact]
    public void IngestUncoveredOnlyDoesNotLoadLeanOrVerifyScribeAndMatchesAlignedBytes()
    {
        var fixture = UncoveredOnlyIngestFixture();
        using var reportFreeRoot = new TemporaryDirectory();
        using var alignedRoot = new TemporaryDirectory();
        WriteDirectoryLedger(reportFreeRoot.Path, fixture.Files);
        WriteDirectoryLedger(alignedRoot.Path, fixture.Files);
        var reportSource = new FakeLeanReportSource(report: null);
        var scribeVerifier = new FakeScribeEmissionVerifier(verification: null);
        var reportFree = new ProductionCliEnvironment(
            reportFreeRoot.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            scribeVerifier);

        var result = reportFree.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);

        var alignedResult = IngestCommand.Run(
            alignedRoot.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty),
            ["--base", "baseline"]);
        Assert.True(alignedResult.Success, alignedResult.Error);
        Assert.Equal(GeneratedIngestImage(alignedRoot), GeneratedIngestImage(reportFreeRoot));
    }

    [Fact]
    public void IngestUncoveredOnlyIsReportFreeAndIdempotentAfterItsLedgerIsAlreadyPresent()
    {
        var fixture = UncoveredOnlyIngestFixture();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var firstRepository = new FakeRepositoryGateway(
            RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var first = new ProductionCliEnvironment(
            temporary.Path,
            firstRepository,
            new FakeLeanReportSource(report: null),
            new FakeScribeEmissionVerifier(verification: null));

        var firstResult = first.Ingest(ReportInputUnchangedArguments);

        Assert.True(firstResult.Success, firstResult.Error);
        var afterFirst = GeneratedIngestImage(temporary);
        var generated = DirectoryLedgerTestSupport.OverlayRepositoryFiles(
            temporary,
            fixture.Files);

        var reportSource = new FakeLeanReportSource(report: null);
        var scribeVerifier = new FakeScribeEmissionVerifier(verification: null);
        var second = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(generated),
                Snapshot(fixture.Baseline)),
            reportSource,
            scribeVerifier);

        var secondResult = second.Ingest(ReportInputUnchangedArguments);

        Assert.True(secondResult.Success, secondResult.Error);
        Assert.Contains("ledger_changed=false", secondResult.Output, StringComparison.Ordinal);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);
        Assert.Equal(afterFirst, GeneratedIngestImage(temporary));
    }

    [Fact]
    public void IngestIgnoresReportInputDeltaWithoutLoadingLean()
    {
        var fixture = UncoveredOnlyIngestFixture();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = GeneratedIngestImage(temporary);
        var reportSource = new FakeLeanReportSource(report: null);
        var scribeVerifier = new FakeScribeEmissionVerifier(verification: null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(["D5/S0/Carrier/Ring.lean"]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            scribeVerifier);

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);
        Assert.NotEqual(before, GeneratedIngestImage(temporary));
    }

    [Fact]
    public void IngestPreservesExistingStatusAuthorityDeltaWithoutLoadingLean()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var existingAtomId = ExistingAtomId(fixture);
        var atomPath = DirectoryAtomPath(existingAtomId, "residual-open");
        fixture.Files[atomPath] = fixture.Files[atomPath].Replace(
            "coverage_gids: []",
            $"coverage_gids:\n  - gid: {coverageGid}\n    target_statement_id: null",
            StringComparison.Ordinal);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = GeneratedIngestImage(temporary);
        var reportSource = new FakeLeanReportSource(report: null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([atomPath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            new FakeScribeEmissionVerifier(verification: null));

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Contains("skipped_existing=1", result.Output, StringComparison.Ordinal);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    [Fact]
    public void IngestPreservesRemovedExistingReceiptedEntryWithoutRestoringIt()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var existingAtomId = ExistingAtomId(fixture);
        var atomPath = DirectoryAtomPath(existingAtomId, "residual-open");
        fixture.Baseline[atomPath] = fixture.Baseline[atomPath]
            .Replace(
                "coverage_gids: []",
                $"coverage_gids:\n  - gid: {coverageGid}\n    target_statement_id: null",
                StringComparison.Ordinal)
            .Replace(
                "  unresolved_subitems: []",
                "  unresolved_subitems:\n    - inherited-open-clause",
                StringComparison.Ordinal);
        Assert.True(fixture.Files.Remove(atomPath));
        var casPath = Assert.Single(fixture.Files.Keys, DigestionCasStore.IsCanonicalPath);
        Assert.True(fixture.Files.Remove(casPath));

        AssertReportFreeExistingPreservedWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([atomPath, casPath]));
    }

    [Fact]
    public void IngestPreservesExistingSourcePathAuthorityDeltaWithoutLoadingTruth()
    {
        const string alternateSourcePath = "docs/GOVERNANCE-copy.md";
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        fixture.Files[alternateSourcePath] = fixture.Files[RuleFixture.FixtureDigestionSourcePath];
        fixture.Files[DirectorySourceMetadataPath()] = fixture.Files[DirectorySourceMetadataPath()]
            .Replace(
                $"path = \"{RuleFixture.FixtureDigestionSourcePath}\"",
                $"path = \"{alternateSourcePath}\"",
                StringComparison.Ordinal);

        AssertReportFreeExistingPreservedWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([alternateSourcePath, DirectorySourceMetadataPath()]));
    }

    [Fact]
    public void IngestPreservesExistingAtomizerAuthorityDeltaWithoutLoadingTruth()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        fixture.Files[DirectorySourceMetadataPath()] = fixture.Files[DirectorySourceMetadataPath()]
            .Replace(
                $"atomizer = \"{AtomizerRegistry.GictId}\"",
                $"atomizer = \"{AtomizerRegistry.PzgId}\"",
                StringComparison.Ordinal);

        AssertReportFreeExistingPreservedWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([DirectorySourceMetadataPath()]));
    }

    [Fact]
    public void IngestPreservesExistingGenreAuthorityDeltaWithoutLoadingTruth()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        fixture.Files[DirectorySourceMetadataPath()] = fixture.Files[DirectorySourceMetadataPath()]
            .Replace(
                "unregistered_genres = []",
                "unregistered_genres = [\"未登记体\"]",
                StringComparison.Ordinal);

        AssertReportFreeExistingPreservedWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([DirectorySourceMetadataPath()]));
    }

    [Fact]
    public void IngestPreservesCoveredEntryExternalAuthorityDeltaWithoutLoadingTruth()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var oldPath = DirectoryAtomPath(ExistingAtomId(fixture), "residual-open");
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[oldPath] = files[oldPath].Replace(
                "coverage_gids: []",
                $"coverage_gids:\n  - gid: {coverageGid}\n    target_statement_id: null",
                StringComparison.Ordinal);
        }

        AssertReportFreeExistingPreservedWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([
                ScribeEmissionAttestation.DefinitionPath(
                    ScribeEmissionAttestation.DocumentGid(coverageGid)),
            ]));
    }

    [Fact]
    public void IngestEmptyChangeSetPreservesCoveredEntryWithoutTruthOrWrites()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var oldPath = DirectoryAtomPath(ExistingAtomId(fixture), "residual-open");
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[oldPath] = files[oldPath].Replace(
                "coverage_gids: []",
                $"coverage_gids:\n  - gid: {coverageGid}\n    target_statement_id: null",
                StringComparison.Ordinal);
        }

        AssertReportFreeExistingPreservedWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create(Array.Empty<string>()));
    }

    [Fact]
    public void IngestDoesNotTransferCoverageToRewrittenContent()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture(rewriteExistingAtom: true);
        var currentBytes = Encoding.UTF8.GetBytes(fixture.Files[RuleFixture.FixtureDigestionSourcePath]);
        var currentAtom = Assert.Single(AtomizerRegistry.Atomize(
            SyntheticNumberedAtomizer.Id,
            currentBytes,
            DigestionTestSupport.Rules).Claims);
        var currentAtomId = AtomId(currentAtom);
        var oldPath = DirectoryAtomPath(ExistingAtomId(fixture), "residual-open");
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[oldPath] = files[oldPath].Replace(
                "coverage_gids: []",
                $"coverage_gids:\n  - gid: {coverageGid}\n    target_statement_id: null",
                StringComparison.Ordinal);
        }

        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var reportSource = new FakeLeanReportSource(report: null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            new FakeScribeEmissionVerifier(verification: null));

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, reportSource.CallCount);
        var entries = BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries();
        Assert.Equal([coverageGid], Assert.Single(
            entries,
            entry => entry.AtomId == ExistingAtomId(fixture)).CoverageGids.ToArray());
        Assert.Empty(Assert.Single(
            entries,
            entry => entry.AtomId == currentAtomId).CoverageGids);
    }

    [Fact]
    public void IngestDoesNotTransferUnresolvedReceiptsToRewrittenContent()
    {
        var fixture = UncoveredOnlyIngestFixture(rewriteExistingAtom: true);
        var oldPath = DirectoryAtomPath(ExistingAtomId(fixture), "residual-open");
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[oldPath] = files[oldPath].Replace(
                "  unresolved_subitems: []",
                "  unresolved_subitems:\n    - inherited-open-clause",
                StringComparison.Ordinal);
        }

        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(report: null),
            new FakeScribeEmissionVerifier(verification: null));

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        var entries = BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries();
        Assert.Equal(["inherited-open-clause"], Assert.Single(
            entries,
            entry => entry.AtomId == ExistingAtomId(fixture)).Receipts.UnresolvedSubitems.ToArray());
        Assert.Empty(Assert.Single(
            entries,
            entry => entry.AtomId != ExistingAtomId(fixture)).Receipts.UnresolvedSubitems);
    }

    [Theory]
    [InlineData("scribe")]
    [InlineData("unresolved")]
    [InlineData("tail")]
    [InlineData("quarantine")]
    [InlineData("cover-disposition")]
    public void IngestPreservesCurrentOnlyReceiptedEntryWithoutTruthOrWrites(
        string receiptKind)
    {
        const string gid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var currentBytes = Encoding.UTF8.GetBytes(
            fixture.Files[RuleFixture.FixtureDigestionSourcePath]);
        var atoms = AtomizerRegistry.Atomize(
            atomizerId,
            currentBytes,
            DigestionTestSupport.Rules).Claims;
        Assert.Equal(2, atoms.Length);
        var newAtom = atoms[1];
        var entry = DigestionTestSupport.Entry(
            newAtom,
            AtomId(newAtom),
            atomizerId,
            sourceId: "fixture-source",
            sourcePath: RuleFixture.FixtureDigestionSourcePath);
        entry = entry with
        {
            Receipts = receiptKind switch
            {
                "scribe" => entry.Receipts with
                {
                    Scribe = [new DigestionScribeReceipt(
                        gid,
                        "sha256:" + new string('b', 64),
                        "sha256:" + new string('c', 64))],
                },
                "unresolved" => entry.Receipts with { UnresolvedSubitems = ["open clause"] },
                "tail" => entry.Receipts with
                {
                    TailAuthorization = new DigestionExternalReceipt(
                        "Evidence/tail.txt",
                        "sha256:" + new string('d', 64)),
                },
                "quarantine" => entry.Receipts with
                {
                    Quarantine = new DigestionQuarantine(
                        "fixture",
                        "fixture cleared",
                        "missing-prerequisite"),
                },
                "cover-disposition" => entry.Receipts with
                {
                    CoverDisposition = new DigestionCoverDisposition(
                        new DigestionStatus(
                            DigestionMigrationState.Residual,
                            DigestionTruthState.Open),
                        [gid],
                        []),
                },
                _ => throw new ArgumentOutOfRangeException(nameof(receiptKind)),
            },
        };
        var currentDocument = IngestLedger(atomizerId, atoms[0]);
        var currentSource = Assert.Single(currentDocument.RequireDigestionSources());
        DirectoryLedgerTestSupport.ReplaceWithProjection(
            fixture.Files,
            currentDocument.WithDigestionSources(
            [
                currentSource with { Entries = currentSource.Entries.Add(entry) },
            ]));
        var capture = DigestionCasStore.Capture(newAtom.RawBytes.AsSpan());
        fixture.Files[capture.RelativePath] = Encoding.UTF8.GetString(capture.Bytes.AsSpan());

        AssertReportFreeExistingPreservedWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([
                DirectoryAtomPath(entry.AtomId, "residual-open"),
                capture.RelativePath,
            ]));
    }

    [Fact]
    public void IngestPreservesCurrentOnlyNonResidualEntryWithoutLoadingTruth()
    {
        var fixture = UncoveredOnlyIngestFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var currentBytes = Encoding.UTF8.GetBytes(
            fixture.Files[RuleFixture.FixtureDigestionSourcePath]);
        var atoms = AtomizerRegistry.Atomize(
            atomizerId,
            currentBytes,
            DigestionTestSupport.Rules).Claims;
        Assert.Equal(2, atoms.Length);
        var newAtom = atoms[1];
        var newEntry = DigestionTestSupport.Entry(
            newAtom,
            AtomId(newAtom),
            atomizerId,
            migration: DigestionMigrationState.Partial,
            truth: DigestionTruthState.Open,
            sourceId: "fixture-source",
            sourcePath: RuleFixture.FixtureDigestionSourcePath);
        var currentDocument = IngestLedger(atomizerId, atoms[0]);
        var currentSource = Assert.Single(currentDocument.RequireDigestionSources());
        DirectoryLedgerTestSupport.ReplaceWithProjection(
            fixture.Files,
            currentDocument.WithDigestionSources(
            [
                currentSource with { Entries = currentSource.Entries.Add(newEntry) },
            ]));
        var capture = DigestionCasStore.Capture(newAtom.RawBytes.AsSpan());
        fixture.Files[capture.RelativePath] = Encoding.UTF8.GetString(capture.Bytes.AsSpan());

        AssertReportFreeExistingPreservedWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([
                RuleFixture.FixtureDigestionSourcePath,
                DirectoryAtomPath(newEntry.AtomId, "partial-open"),
                capture.RelativePath,
            ]));
    }

    [Fact]
    public void IngestPreservesPlannedExistingEntryRewriteWithoutLoadingTruth()
    {
        const string sourceText = """
            # PZG

            **定理 18.7(时间之矢)**。first clause。

            **推论:第二子句**;the full plan has two clauses。

            """;
        var fixture = new RuleFixture();
        var sourceBytes = Encoding.UTF8.GetBytes(sourceText);
        var parent = Assert.Single(PzgAtomizer.Atomize(
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var ledger = MapOnlyEntry(IngestLedger(AtomizerRegistry.PzgId, parent), entry => entry with
        {
            Receipts = entry.Receipts with
            {
                UnresolvedSubitems = ["second clause"],
            },
        });
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = sourceText;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = sourceText;
        InstallProjectedLedger(fixture, ledger, parent);

        AssertReportFreeExistingPreservedWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create(Array.Empty<string>()));
    }

    [Fact]
    public void IngestReportFreePreservesStructurallyInvalidExistingLedgerWithoutWriting()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes(fixture.Files[RuleFixture.FixtureDigestionSourcePath]);
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, atom);
        var source = Assert.Single(ledger.RequireDigestionSources());
        ledger = ledger.WithDigestionSources([
            source with
            {
                SourceId = "INVALID",
                Entries = source.Entries.Select(entry => entry with
                {
                    SourceId = "INVALID",
                }).ToImmutableArray(),
            },
        ]);
        InstallProjectedLedger(fixture, ledger, atom);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = GeneratedIngestImage(temporary);
        var reportSource = new FakeLeanReportSource(report: null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            new FakeScribeEmissionVerifier(verification: null));

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    [Fact]
    public void IngestReportFreePreservesEntryWithMissingExistingCasWithoutWrites()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var casPath = Assert.Single(fixture.Files.Keys, DigestionCasStore.IsCanonicalPath);
        Assert.True(fixture.Files.Remove(casPath));

        AssertReportFreeExistingPreservedWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([casPath]));
    }

    [Fact]
    public void IngestReportFreeSkipsExistingAtomWithHashMismatchedCasWithoutTruthOrWrites()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var casPath = Assert.Single(fixture.Files.Keys, DigestionCasStore.IsCanonicalPath);
        fixture.Files[casPath] = "tampered atom bytes\n";
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var casOutputPath = Path.Combine(
            temporary.Path,
            casPath.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(casOutputPath)!);
        File.WriteAllText(casOutputPath, fixture.Files[casPath], new UTF8Encoding(false));
        var before = GeneratedIngestImage(temporary);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([casPath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(report: null),
            new FakeScribeEmissionVerifier(verification: null));

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Contains("skipped_existing=1", result.Output, StringComparison.Ordinal);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    [Fact]
    public void IngestReportFreePreservesChangedStatusAuthorityWhenProjectedStatusWouldDrift()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes(fixture.Files[RuleFixture.FixtureDigestionSourcePath]);
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var ledger = MapOnlyEntry(IngestLedger(atomizerId, atom), entry => entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        });
        InstallProjectedLedger(fixture, ledger, atom);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = GeneratedIngestImage(temporary);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(report: null),
            new FakeScribeEmissionVerifier(verification: null));

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Contains("skipped_existing=1", result.Output, StringComparison.Ordinal);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    private static RuleFixture UncoveredOnlyIngestFixture(
        bool addNewAtom = true,
        bool rewriteExistingAtom = false)
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldText = "# Synthetic\n\n**定理 1.1(A)**。old。\n";
        var currentText = rewriteExistingAtom
            ? "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n"
            : addNewAtom
                ? oldText + "\n**定理 1.2(B)**。new。\n"
                : oldText;
        var oldBytes = Encoding.UTF8.GetBytes(oldText);
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            oldBytes,
            DigestionTestSupport.Rules).Claims);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = currentText;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = oldText;
        InstallProjectedLedger(fixture, IngestLedger(atomizerId, oldAtom), oldAtom);
        return fixture;
    }

    private static string ExistingAtomId(RuleFixture fixture)
    {
        var baselineBytes = Encoding.UTF8.GetBytes(
            fixture.Baseline[RuleFixture.FixtureDigestionSourcePath]);
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            SyntheticNumberedAtomizer.Id,
            baselineBytes,
            DigestionTestSupport.Rules).Claims);
        return AtomId(atom);
    }

    private static void AssertReportFreeExistingPreservedWithoutTruthOrWrites(
        RuleFixture fixture,
        RawChangeSet changes)
    {
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = GeneratedIngestImage(temporary);
        var reportSource = new FakeLeanReportSource(report: null);
        var scribeVerifier = new FakeScribeEmissionVerifier(verification: null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                changes,
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            scribeVerifier);

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Contains("skipped_existing=", result.Output, StringComparison.Ordinal);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    private static string GeneratedIngestImage(TemporaryDirectory repository) =>
        DirectoryLedgerTestSupport.RepositoryImage(repository);

    private static string DirectorySourceMetadataPath() =>
        $"{BackfillInventoryLoader.RootPath}fixture-source/source.toml";
}
