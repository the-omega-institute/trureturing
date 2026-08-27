using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void CasBackedLegacyBoundaryDoesNotContributeSourceOrBoundaryGaps()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var document = Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Open);
        var snapshot = Snapshot((captured.RelativePath, captured.Bytes.ToArray()));

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            snapshot,
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, status.Alignment);
        Assert.DoesNotContain(status.Gaps, static gap =>
            gap.Code == "source-missing" || gap.Code.Contains("boundary", StringComparison.Ordinal));
    }

    [Fact]
    public void CasBackedNoAtomizerBoundaryStillRequiresItsSpecificationSource()
    {
        var source = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var atom = new DigestionAtom(
            "manual/receipt",
            0,
            source.Length,
            ImmutableArray.CreateRange(source),
            DigestionFingerprint.Compute(source),
            ImmutableArray<DigestionContext>.Empty);
        var captured = DigestionCasStore.Capture(source);
        var document = Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Open,
            atomizer: AtomizerRegistry.NoAtomizerId);
        var snapshot = Snapshot((captured.RelativePath, captured.Bytes.ToArray()));

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            snapshot,
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.LegacyBoundary, status.Alignment);
        Assert.Contains(status.Gaps, static gap => gap.Code == "source-missing");
    }

    [Fact]
    public void IngestRebindsCasBackedNoAtomizerBoundaryAndRemainsByteIdempotent()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var atom = new DigestionAtom(
            "manual/receipt",
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            ImmutableArray<DigestionContext>.Empty);
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Open,
            atomizer: AtomizerRegistry.NoAtomizerId);

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", sourceBytes), CasFile(atom)),
            ledger);
        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        var migrated = first.Document;

        var migratedEntry = Assert.Single(migrated.RequireDigestionEntries());
        Assert.NotNull(migratedEntry.Boundary);
        Assert.Equal(atom.Fingerprints.RawSha256, migratedEntry.CasRef);
        Assert.Empty(first.CasObjects);

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(
                ("docs/source.md", sourceBytes),
                CasFile(atom)),
            ledger);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes, secondBytes);
    }

    [Fact]
    public void IngestOnboardsRegisteredEmptySourceAndRemainsByteIdempotent()
    {
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。first。\n\n**定理 1.2(B)**。second。\n");
        var atoms = AtomizerRegistry.Atomize(atomizerId, sourceBytes, DigestionTestSupport.Rules).Claims;
        var ledger = EmptyDocument(atomizerId);

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", sourceBytes)),
            ledger);
        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        var migrated = first.Document;
        var entries = Assert.Single(first.Document.RequireDigestionSources()).Entries;

        Assert.Equal(atoms.Length, first.ResidualOpenAdded);
        Assert.Equal(atoms.Length, entries.Length);
        Assert.Equal(atoms.Length, first.CasObjects.Length);
        Assert.Empty(first.Fallbacks);
        Assert.All(entries, static entry =>
        {
            Assert.Null(entry.Boundary);
            Assert.Equal(entry.Fingerprints.RawSha256, entry.CasRef);
            Assert.Empty(entry.CoverageGids);
            Assert.Empty(entry.Receipts.Coverage);
            Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
        });
        Assert.All(first.CasObjects, item => Assert.Contains(
            atoms,
            atom => atom.Fingerprints.RawSha256 == item.Reference
                && atom.RawBytes.AsSpan().SequenceEqual(item.Bytes.AsSpan())));

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, first.CasObjects),
            ledger);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes, secondBytes);
    }

    [Fact]
    public void UnchangedSingleClauseLedgerReplayRemainsByteIdentical()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。single clause。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var document = StructuralLedger(atom);
        var expected = DirectoryLedgerTestSupport.Image(document);

        var replay = DigestionIngestor.Plan(
            document,
            Snapshot(("docs/source.md", sourceBytes), CasFile(atom)),
            document);

        Assert.Equal(0, replay.ResidualOpenAdded);
        Assert.Empty(replay.CasObjects);
        Assert.Equal(expected, DirectoryLedgerTestSupport.Image(replay.Document));
    }

    [Fact]
    public void DanglingChainIdRetainsChainMigrationIncompleteGap()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。single clause。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var document = StructuralLedger(atom);
        var source = Assert.Single(document.RequireDigestionSources());
        var entry = Assert.Single(source.Entries);
        document = document.WithDigestionSources(
        [
            source with
            {
                Entries = [entry with { Receipts = entry.Receipts with { ChainAtoms = ["missing-child"] } }],
            },
        ]);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            Snapshot(("docs/source.md", sourceBytes), CasFile(atom)),
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Contains(status.Gaps, gap =>
            gap.Code == "chain-migration-incomplete" && gap.Detail == "missing-child");
        Assert.False(status.Deletable);
    }

    [Fact]
    public void DerivedChainAbsorptionReachesFixedPointAcrossThreeLevels()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("manual fixed-point receipt\n");
        var atom = new DigestionAtom(
            "manual/fixed-point",
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            ImmutableArray<DigestionContext>.Empty);
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var template = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            gid,
            new DigestionCoverageReceipt(
                gid,
                atom.Fingerprints.RawSha256,
                DigestionFingerprint.Compute(target).RawSha256),
            new DigestionScribeReceipt(gid, definitionHash, emissionHash),
            atomizer: AtomizerRegistry.NoAtomizerId);
        var source = Assert.Single(template.RequireDigestionSources());
        var entry = Assert.Single(source.Entries);
        var chained = template.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    entry with
                    {
                        AtomId = "chain-parent",
                        Receipts = entry.Receipts with { ChainAtoms = ["chain-middle"] },
                    },
                    entry with
                    {
                        AtomId = "chain-middle",
                        Receipts = entry.Receipts with { ChainAtoms = ["chain-leaf"] },
                    },
                    entry with { AtomId = "chain-leaf" },
                ],
            },
        ]);
        var record = new ScribeEmissionRecord(
            gid,
            ScribeEmissionAttestation.DefinitionPath(gid),
            definitionHash,
            ScribeEmissionAttestation.EmissionPath(gid),
            emissionHash);
        var rawSnapshot = RawRepositorySnapshot.Create(
        [
            new RawRepositoryEntry("docs/source.md", ImmutableArray.CreateRange(sourceBytes)),
            new RawRepositoryEntry(CasFile(atom).Path, ImmutableArray.CreateRange(CasFile(atom).Bytes)),
            new RawRepositoryEntry(targetPath, ImmutableArray.CreateRange(target)),
            new RawRepositoryEntry(record.DefinitionPath, ImmutableArray.CreateRange(definition)),
            new RawRepositoryEntry(record.EmissionPath, ImmutableArray.CreateRange(emission)),
        ]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(rawSnapshot)).Snapshot;

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            chained,
            snapshot,
            AcceptedLean(targetPath),
            VerifiedScribeEmissions.Create([record]),
            baselineDocument: chained);

        Assert.Equal(3, evaluation.Entries.Length);
        Assert.All(evaluation.Entries, static item => Assert.Equal(
            DigestionMigrationState.Absorbed,
            item.DerivedStatus.Migration));
        Assert.DoesNotContain(evaluation.Entries.SelectMany(static item => item.Gaps), static gap =>
            gap.Code == "chain-migration-incomplete");
    }

    [Fact]
    public void IngestOnboardsRegisteredEmptySourceWithCoarseFallback()
    {
        const string sourcePath = "docs/develop/theory/non-utf8.bin";
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = new byte[] { 0xff, 0x00, 0xfe };
        var ledger = Document(
            atomizerId,
            [],
            sourcePath: sourcePath,
            genreRegistryCheck: GenreRegistryCheck.Collected([]));

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot((sourcePath, sourceBytes)),
            ledger);
        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        var migrated = first.Document;

        var fallback = Assert.Single(first.Fallbacks);
        Assert.Equal("source", fallback.SourceId);
        Assert.Contains("Unicode", fallback.Reason, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(1, first.ResidualOpenAdded);
        var coarse = Assert.Single(first.Document.RequireDigestionEntries());
        Assert.Equal("coarse/source", coarse.AstPath);
        Assert.Equal(DigestionMigrationState.Residual, coarse.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, coarse.ProjectedStatus.Truth);
        var captured = Assert.Single(first.CasObjects);
        Assert.Equal(coarse.Fingerprints.RawSha256, coarse.CasRef);
        Assert.Equal(sourceBytes, captured.Bytes.ToArray());

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(first.CasObjects
                .Select(static item => (item.RelativePath, item.Bytes.ToArray()))
                .Prepend((sourcePath, sourceBytes))
                .ToArray()),
            ledger);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes, secondBytes);
    }

    [Fact]
    public void DerivationRejectsHandwrittenStatusThatClaimsMoreThanReceiptsProve()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var snapshot = Snapshot(
            ("docs/source.md", source),
            CasFile(atom),
            ("D5/X_Frontier/Probe.lean", Encoding.UTF8.GetBytes(Lean("D5/X_Frontier/Probe"))));
        var lean = AcceptedLean("D5/X_Frontier/Probe.lean");
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed);

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            ledger,
            snapshot,
            lean,
            baselineDocument: ledger);
        var status = Assert.Single(evaluation.Entries);

        Assert.Equal(DigestionMigrationState.Partial, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.False(status.Deletable);
        Assert.Contains(status.Gaps, gap => gap.Code == "coverage-receipt-missing");
        Assert.Contains(evaluation.Findings, finding =>
            finding.Contains("handwritten status", StringComparison.Ordinal));
    }

    [Fact]
    public void ReproducibleExtractionWithoutSemanticTargetRemainsResidual()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Residual,
            DigestionTruthState.Open,
            includeCoverageGid: false);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            ledger,
            Snapshot(("docs/source.md", source), CasFile(atom)),
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: ledger).Entries);

        Assert.Equal(DigestionMigrationState.Residual, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.Contains(status.Gaps, gap => gap.Code == "coverage-gid-missing");
    }

    [Fact]
    public void UnregisteredGenreDebtDoesNotChangeClosedTruthButPreventsDeletion()
    {
        const string token = "**新判词。**";
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var source = Encoding.UTF8.GetBytes($"# Observer\n\n{token} claim。\n");
        var atom = Assert.Single(ObserverAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var record = new ScribeEmissionRecord(
            gid,
            ScribeEmissionAttestation.DefinitionPath(gid),
            definitionHash,
            ScribeEmissionAttestation.EmissionPath(gid),
            emissionHash);
        var loaded = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            gid,
            new DigestionCoverageReceipt(
                gid,
                atom.Fingerprints.RawSha256,
                DigestionFingerprint.Compute(target).RawSha256),
            new DigestionScribeReceipt(gid, definitionHash, emissionHash),
            atomizer: AtomizerRegistry.ObserverId);
        var document = loaded.WithDigestionSources(
        [
            Assert.Single(loaded.RequireDigestionSources()) with
            {
                GenreRegistryProjection = GenreRegistryProjection.Available(
                    GenreRegistryCheck.Collected([token])),
            },
        ]);
        var snapshot = Snapshot(
            ("docs/source.md", source),
            CasFile(atom),
            (targetPath, target),
            (record.DefinitionPath, definition),
            (record.EmissionPath, emission));

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            snapshot,
            AcceptedLean(targetPath),
            VerifiedScribeEmissions.Create([record]),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionMigrationState.Absorbed, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, status.DerivedStatus.Truth);
        var gap = Assert.Single(status.Gaps);
        Assert.Equal("unregistered-genre", gap.Code);
        Assert.Equal(token, gap.Detail);
        Assert.False(status.Deletable);
    }

    [Fact]
    public void StructuralRawSeenReplacesTheBoundaryPrerequisite()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var document = StructuralLedger(atom);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            Snapshot(("docs/source.md", source), CasFile(atom)),
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, status.Alignment);
        Assert.DoesNotContain(status.Gaps, gap => gap.Code.Contains("boundary", StringComparison.Ordinal));
        Assert.DoesNotContain(status.Gaps, gap => gap.Code == "normalized-seen-not-deletable");
    }

    [Fact]
    public void CasReceiptRemainsSeenAcrossNormalizedSourceRewrite()
    {
        var ledgerBytes = Encoding.UTF8.GetBytes(
            "# GICT\r\n\r\n**定理 1.1(Test)**。claim。\r\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(ledgerBytes, DigestionTestSupport.Rules).Claims);
        var document = StructuralLedger(atom);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            Snapshot(("docs/source.md", currentBytes), CasFile(atom)),
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, status.Alignment);
        Assert.False(status.Deletable);
        Assert.DoesNotContain(status.Gaps, gap => gap.Code == "normalized-seen-not-deletable");
    }

    private static DigestionEntryEvaluation EvaluateDeclarationCoverage(
        string declarationGid,
        IEnumerable<string> describedDeclarations,
        bool includeCommittedEmission = true)
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        const string moduleGid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean(moduleGid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var record = new ScribeEmissionRecord(
            moduleGid,
            ScribeEmissionAttestation.DefinitionPath(moduleGid),
            definitionHash,
            ScribeEmissionAttestation.EmissionPath(moduleGid),
            emissionHash);
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            declarationGid,
            new DigestionCoverageReceipt(
                declarationGid,
                atom.Fingerprints.RawSha256,
                DigestionFingerprint.Compute(target).RawSha256),
            new DigestionScribeReceipt(declarationGid, definitionHash, emissionHash));
        var snapshotFiles = new List<(string Path, byte[] Bytes)>
        {
            ("docs/source.md", source),
            CasFile(atom),
            (targetPath, target),
            (ScribeEmissionAttestation.DefinitionPath(moduleGid), definition),
        };
        if (includeCommittedEmission)
        {
            snapshotFiles.Add((ScribeEmissionAttestation.EmissionPath(moduleGid), emission));
        }
        var snapshot = Snapshot([.. snapshotFiles]);

        return Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            ledger,
            snapshot,
            AcceptedLean(targetPath),
            VerifiedScribeEmissions.Create([record], describedDeclarations),
            baselineDocument: ledger).Entries);
    }

    private static DigestionEntryEvaluation EvaluateCompleteTail(
        string authorizationPath,
        byte[] authorization,
        string? recordedSha256 = null,
        RawChangeSet? changes = null)
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        const string gid = "D5/X_Assumptions/Probe";
        const string targetPath = "D5/X_Assumptions/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Tail,
            gid,
            new DigestionCoverageReceipt(
                gid,
                atom.Fingerprints.RawSha256,
                DigestionFingerprint.Compute(target).RawSha256),
            new DigestionScribeReceipt(gid, definitionHash, emissionHash),
            tailAuthorization: new DigestionExternalReceipt(
                authorizationPath,
                recordedSha256 ?? DigestionFingerprint.Compute(authorization).RawSha256));
        var attestation = ScribeEmissionAttestation.Write(
        [
            new ScribeEmissionRecord(
                gid,
                ScribeEmissionAttestation.DefinitionPath(gid),
                definitionHash,
                ScribeEmissionAttestation.EmissionPath(gid),
                emissionHash),
        ]).ToArray();
        var report = new LeanFileReport(
            ImmutableArray<string>.Empty,
            [new LeanDeclaration("tailProbe", "axiom", "True", ["tailProbe"])]);
        var snapshot = Snapshot(
            ("docs/source.md", source),
            CasFile(atom),
            (targetPath, target),
            (ScribeEmissionAttestation.DefinitionPath(gid), definition),
            (ScribeEmissionAttestation.EmissionPath(gid), emission),
            (ScribeEmissionAttestation.RelativePath, attestation),
            (authorizationPath, authorization));

        var verifiedEmissions = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                gid,
                ScribeEmissionAttestation.DefinitionPath(gid),
                definitionHash,
                ScribeEmissionAttestation.EmissionPath(gid),
                emissionHash),
        ]);
        return Assert.Single(DigestionStatusEvaluator.Evaluate(
            changes is null
                ? DigestionEvaluationScope.FullScan
                : DigestionEvaluationScope.ChangedSet,
            ledger,
            snapshot,
            AcceptedLean((targetPath, report)),
            verifiedEmissions,
            changes: changes,
            baselineDocument: ledger).Entries);
    }

    private static BackfillInventoryDocument Ledger(
        DigestionAtom atom,
        DigestionMigrationState migration,
        DigestionTruthState truth,
        string coverageGid = "D5/X_Frontier/Probe",
        DigestionCoverageReceipt? coverageReceipt = null,
        DigestionScribeReceipt? scribeReceipt = null,
        string atomizer = AtomizerRegistry.GictId,
        bool includeCoverageGid = true,
        bool includeBoundary = true,
        DigestionExternalReceipt? tailAuthorization = null)
    {
        var receipts = new DigestionReceipts(
            coverageReceipt is null ? [] : [coverageReceipt],
            scribeReceipt is null ? [] : [scribeReceipt],
            [],
            [],
            tailAuthorization);
        var entry = DigestionTestSupport.Entry(
            atom,
            "gict-1.1",
            atomizer,
            migration,
            truth,
            includeCoverageGid ? [coverageGid] : [],
            receipts,
            includeBoundary,
            AtomizerRegistry.GictId);
        return DigestionTestSupport.Document(
            atomizer,
            [entry],
            AtomizerRegistry.GictId);
    }

    private static BackfillInventoryDocument StructuralLedger(DigestionAtom atom)
    {
        var document = Ledger(
            atom,
            DigestionMigrationState.Residual,
            DigestionTruthState.Open,
            includeCoverageGid: false,
            includeBoundary: false);
        var source = Assert.Single(document.RequireDigestionSources());
        return document.WithDigestionSources(
        [
            source with
            {
                GenreRegistryProjection = GenreRegistryProjection.Available(
                    GenreRegistryCheck.Collected([])),
            },
        ]);
    }

    private static (BackfillInventoryDocument Ledger, DigestionCasObject Captured)
        CasBackedNoAtomizerLedger(byte[] receiptBytes)
    {
        var atom = new DigestionAtom(
            "manual/receipt",
            0,
            receiptBytes.Length,
            ImmutableArray.CreateRange(receiptBytes),
            DigestionFingerprint.Compute(receiptBytes),
            ImmutableArray<DigestionContext>.Empty);
        return (Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Open,
            atomizer: AtomizerRegistry.NoAtomizerId), DigestionCasStore.Capture(receiptBytes));
    }
}
