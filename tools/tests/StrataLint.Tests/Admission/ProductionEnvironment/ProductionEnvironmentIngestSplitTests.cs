using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private static readonly string[] ReportInputUnchangedArguments =
        ["--base", "baseline", "--report-input-state", "unchanged"];

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
    public void IngestRejectsReportInputDeltaBeforeLoadingLeanOrWriting()
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

        var result = environment.Ingest(
            ["--base", "baseline", "--report-input-state", "changed"]);

        Assert.False(result.Success);
        Assert.Contains("INGEST_TRUTH_ALIGNMENT_REQUIRED", result.Error, StringComparison.Ordinal);
        Assert.Contains("make align-digestion-status", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    [Fact]
    public void IngestRejectsExistingStatusAuthorityDeltaBeforeLoadingLeanOrWriting()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var atomPath = DirectoryAtomPath("old-receipt", "residual-open");
        fixture.Files[atomPath] = fixture.Files[atomPath].Replace(
            "coverage_gids: []",
            $"coverage_gids:\n  - {coverageGid}",
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

        Assert.False(result.Success);
        Assert.Contains("INGEST_TRUTH_ALIGNMENT_REQUIRED", result.Error, StringComparison.Ordinal);
        Assert.Contains("existing entry", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    [Fact]
    public void IngestRejectsRemovedExistingReceiptedEntryBeforeLoadingTruthOrWriting()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var atomPath = DirectoryAtomPath("old-receipt", "residual-open");
        fixture.Baseline[atomPath] = fixture.Baseline[atomPath]
            .Replace(
                "coverage_gids: []",
                $"coverage_gids:\n  - {coverageGid}",
                StringComparison.Ordinal)
            .Replace(
                "  unresolved_subitems: []",
                "  unresolved_subitems:\n    - inherited-open-clause",
                StringComparison.Ordinal);
        Assert.True(fixture.Files.Remove(atomPath));
        var casPath = Assert.Single(fixture.Files.Keys, DigestionCasStore.IsCanonicalPath);
        Assert.True(fixture.Files.Remove(casPath));

        AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([atomPath, casPath]),
            "existing entry old-receipt removed");
    }

    [Fact]
    public void IngestRejectsExistingSourcePathAuthorityDeltaBeforeLoadingTruthOrWriting()
    {
        const string alternateSourcePath = "docs/GOVERNANCE-copy.md";
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        fixture.Files[alternateSourcePath] = fixture.Files[RuleFixture.FixtureDigestionSourcePath];
        fixture.Files[DirectorySourceMetadataPath()] = fixture.Files[DirectorySourceMetadataPath()]
            .Replace(
                $"path = \"{RuleFixture.FixtureDigestionSourcePath}\"",
                $"path = \"{alternateSourcePath}\"",
                StringComparison.Ordinal);

        AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([alternateSourcePath, DirectorySourceMetadataPath()]),
            "existing entry");
    }

    [Fact]
    public void IngestRejectsExistingAtomizerAuthorityDeltaBeforeLoadingTruthOrWriting()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        fixture.Files[DirectorySourceMetadataPath()] = fixture.Files[DirectorySourceMetadataPath()]
            .Replace(
                $"atomizer = \"{AtomizerRegistry.GictId}\"",
                $"atomizer = \"{AtomizerRegistry.PzgId}\"",
                StringComparison.Ordinal);

        AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([DirectorySourceMetadataPath()]),
            "existing entry");
    }

    [Fact]
    public void IngestRejectsExistingGenreAuthorityDeltaBeforeLoadingTruthOrWriting()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        fixture.Files[DirectorySourceMetadataPath()] = fixture.Files[DirectorySourceMetadataPath()]
            .Replace(
                "unregistered_genres = []",
                "unregistered_genres = [\"未登记体\"]",
                StringComparison.Ordinal);

        AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([DirectorySourceMetadataPath()]),
            "existing entry");
    }

    [Fact]
    public void IngestRejectsCoveredEntryExternalAuthorityDeltaBeforeLoadingTruthOrWriting()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var oldPath = DirectoryAtomPath("old-receipt", "residual-open");
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[oldPath] = files[oldPath].Replace(
                "coverage_gids: []",
                $"coverage_gids:\n  - {coverageGid}",
                StringComparison.Ordinal);
        }

        AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([
                ScribeEmissionAttestation.DefinitionPath(
                    ScribeEmissionAttestation.DocumentGid(coverageGid)),
            ]),
            "covered entry");
    }

    [Fact]
    public void IngestEmptyChangeSetWithCoveredEntryRequiresTruthAlignmentBeforeTruthOrWrites()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var oldPath = DirectoryAtomPath("old-receipt", "residual-open");
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[oldPath] = files[oldPath].Replace(
                "coverage_gids: []",
                $"coverage_gids:\n  - {coverageGid}",
                StringComparison.Ordinal);
        }

        AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create(Array.Empty<string>()),
            "covered entry");
    }

    [Fact]
    public void IngestRejectsCoverageBearingPlannedEntryBeforeLoadingLeanOrWriting()
    {
        const string coverageGid = "D5/S0/Carrier/Ring.goldenRing";
        var fixture = UncoveredOnlyIngestFixture(rewriteExistingAtom: true);
        var currentBytes = Encoding.UTF8.GetBytes(fixture.Files[RuleFixture.FixtureDigestionSourcePath]);
        var currentAtom = Assert.Single(AtomizerRegistry.Atomize(
            SyntheticNumberedAtomizer.Id,
            currentBytes,
            DigestionTestSupport.Rules).Claims);
        var currentAtomId = "gict-residual-"
            + currentAtom.Fingerprints.RawSha256["sha256:".Length..];
        var receipt = new DigestionFormalizationReceipt(
            currentAtomId,
            coverageGid,
            new DigestionFormalizationSignature("goldenRing", "def", "Nat"),
            currentAtom.Fingerprints.RawSha256,
            currentAtom.Fingerprints.RawSha256);
        var receiptPath = DigestionFormalizationReceipt.PathForAtom(currentAtomId);
        var receiptText = Encoding.UTF8.GetString(DigestionFormalizationReceipt.Write(receipt).AsSpan());
        fixture.Files[receiptPath] = receiptText;
        fixture.Baseline[receiptPath] = receiptText;
        var oldPath = DirectoryAtomPath("old-receipt", "residual-open");
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[oldPath] = files[oldPath].Replace(
                "coverage_gids: []",
                $"coverage_gids:\n  - {coverageGid}",
                StringComparison.Ordinal);
        }

        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = GeneratedIngestImage(temporary);
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

        Assert.False(result.Success);
        Assert.Contains("INGEST_TRUTH_ALIGNMENT_REQUIRED", result.Error, StringComparison.Ordinal);
        Assert.Contains("coverage-bearing", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    [Fact]
    public void IngestRejectsReceiptBearingNewEntryBeforeLoadingTruthOrWriting()
    {
        var fixture = UncoveredOnlyIngestFixture(rewriteExistingAtom: true);
        var oldPath = DirectoryAtomPath("old-receipt", "residual-open");
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[oldPath] = files[oldPath].Replace(
                "  unresolved_subitems: []",
                "  unresolved_subitems:\n    - inherited-open-clause",
                StringComparison.Ordinal);
        }

        AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
            "carries receipts");
    }

    [Theory]
    [InlineData("coverage")]
    [InlineData("scribe")]
    [InlineData("unresolved")]
    [InlineData("chain")]
    [InlineData("tail")]
    [InlineData("quarantine")]
    [InlineData("cover-disposition")]
    public void IngestRejectsEveryReceiptKindOnCurrentOnlyNewEntryBeforeTruthOrWrites(
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
            "gict-residual-" + newAtom.Fingerprints.RawSha256["sha256:".Length..],
            atomizerId,
            sourceId: "fixture-source",
            sourcePath: RuleFixture.FixtureDigestionSourcePath);
        entry = entry with
        {
            Receipts = receiptKind switch
            {
                "coverage" => entry.Receipts with
                {
                    Coverage = [new DigestionCoverageReceipt(
                        gid,
                        newAtom.Fingerprints.RawSha256,
                        "sha256:" + new string('a', 64))],
                },
                "scribe" => entry.Receipts with
                {
                    Scribe = [new DigestionScribeReceipt(
                        gid,
                        "sha256:" + new string('b', 64),
                        "sha256:" + new string('c', 64))],
                },
                "unresolved" => entry.Receipts with { UnresolvedSubitems = ["open clause"] },
                "chain" => entry.Receipts with { ChainAtoms = ["old-receipt"] },
                "tail" => entry.Receipts with
                {
                    TailAuthorization = new DigestionExternalReceipt(
                        "Evidence/tail.txt",
                        "sha256:" + new string('d', 64)),
                },
                "quarantine" => entry.Receipts with
                {
                    Quarantine = new DigestionQuarantine("fixture", "fixture cleared"),
                },
                "cover-disposition" => entry.Receipts with
                {
                    CoverDisposition = new DigestionCoverDisposition(
                        new DigestionStatus(
                            DigestionMigrationState.Residual,
                            DigestionTruthState.Open),
                        [gid],
                        [],
                        new DateTimeOffset(2026, 8, 28, 0, 0, 0, TimeSpan.Zero)),
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

        AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([
                DirectoryAtomPath(entry.AtomId, "residual-open"),
                capture.RelativePath,
            ]),
            "carries receipts");
    }

    [Fact]
    public void IngestRejectsNonResidualOpenNewEntryBeforeLoadingTruthOrWriting()
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
            "gict-residual-" + newAtom.Fingerprints.RawSha256["sha256:".Length..],
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

        AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create([
                RuleFixture.FixtureDigestionSourcePath,
                DirectoryAtomPath(newEntry.AtomId, "partial-open"),
                capture.RelativePath,
            ]),
            "projected status is not residual-open");
    }

    [Fact]
    public void IngestRejectsPlannedExistingEntryRewriteBeforeLoadingTruthOrWriting()
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

        AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
            fixture,
            RawChangeSet.Create(Array.Empty<string>()),
            "planned rewrite of existing entry");
    }

    [Fact]
    public void IngestReportFreeRejectsStructurallyInvalidLedgerWithoutWriting()
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

        Assert.False(result.Success);
        Assert.Contains("invalid source_id: INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    [Fact]
    public void IngestReportFreeRejectsChangedStatusAuthorityWhenProjectedStatusWouldDrift()
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

        Assert.False(result.Success);
        Assert.Contains("report-free digest status is invalid", result.Error, StringComparison.Ordinal);
        Assert.Contains("handwritten status partial-open differs from derived residual-open", result.Error, StringComparison.Ordinal);
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

    private static void AssertReportFreeTruthAlignmentRequiredWithoutTruthOrWrites(
        RuleFixture fixture,
        RawChangeSet changes,
        string witness)
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

        Assert.False(result.Success);
        Assert.Contains("INGEST_TRUTH_ALIGNMENT_REQUIRED", result.Error, StringComparison.Ordinal);
        Assert.Contains(witness, result.Error, StringComparison.Ordinal);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    private static string GeneratedIngestImage(TemporaryDirectory repository) =>
        DirectoryLedgerTestSupport.RepositoryImage(repository);

    private static string DirectorySourceMetadataPath() =>
        $"{BackfillInventoryLoader.RootPath}fixture-source/source.toml";
}
