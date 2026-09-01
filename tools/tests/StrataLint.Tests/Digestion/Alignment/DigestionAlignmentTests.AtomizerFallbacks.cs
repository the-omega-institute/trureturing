using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void IngestStatusAuthorityRejectionSurvivesDecoderFallbackContentWideMatch()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("whole source bytes\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var capture = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var baselineEntry = Entry("baseline", coarse) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        };

        var result = DigestionLedgerAligner.Evaluate(
            Ledger([], candidateEntry),
            Snapshot(sourceBytes, [capture]),
            Ledger([], baselineEntry),
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => throw new TheorySourceFormatException("synthetic parse failure"));

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(coarse)));
        Assert.Null(result.AtomFor(AtomId(coarse)));
    }

    [Fact]
    public void IngestStatusAuthorityRejectionSurvivesZeroClaimContentWideMatch()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("not a recognised claim\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var capture = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var baselineEntry = Entry("baseline", coarse) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        };

        var result = DigestionLedgerAligner.Evaluate(
            Ledger([], candidateEntry),
            Snapshot(sourceBytes, [capture]),
            Ledger([], baselineEntry),
            DigestionAlignmentMode.Ingest);

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(coarse)));
        Assert.Null(result.AtomFor(AtomId(coarse)));
    }

    [Fact]
    public void IngestRejectsAtomizerHashFailureInsteadOfFallingBack()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var corrupt = new DigestionAtom(
            0,
            1,
            sourceBytes,
            new DigestionFingerprints(
                "sha256:" + new string('0', 64),
                "sha256:" + new string('0', 64)),
            []);
        var corruptDocument = new AtomizedTheoryDocument(
            [corrupt],
            [new DigestionSlice(true, sourceBytes)],
            GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [oldCapture]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => corruptDocument);

        Assert.Empty(result.Fallbacks);
        Assert.Contains(result.Findings, finding =>
            finding.Contains("fingerprint", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void IngestRejectsAtomPayloadThatDiffersFromItsSourceSpan()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var fabricatedBytes = ImmutableArray.Create((byte)'b');
        var fabricated = new DigestionAtom(
            0,
            1,
            fabricatedBytes,
            DigestionFingerprint.Compute(fabricatedBytes.AsSpan()),
            []);
        var fabricatedDocument = new AtomizedTheoryDocument(
            [fabricated],
            [new DigestionSlice(true, sourceBytes)],
            GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [oldCapture]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => fabricatedDocument);

        Assert.Empty(result.Fallbacks);
        Assert.Empty(result.Residual);
        Assert.Contains(result.Findings, finding =>
            finding.Contains("source span", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void IngestRejectsZeroClaimAtomizerOutputThatDoesNotReassembleTheSource()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var corrupt = new AtomizedTheoryDocument(
            [],
            [new DigestionSlice(false, ImmutableArray.Create((byte)'b'))],
            GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [oldCapture]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => corrupt);

        Assert.Empty(result.Fallbacks);
        Assert.Empty(result.Residual);
        Assert.Contains(result.Findings, finding =>
            finding.Contains("reassemble", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void IngestRefusesZeroClaimCoarseFallbackWhenBaselineHasFineReceipt()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var snapshot = Snapshot(sourceBytes.ToArray(), [oldCapture]);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Ingest);

        var finding = Assert.Single(result.Findings);
        Assert.Contains("source source", finding, StringComparison.Ordinal);
        Assert.Contains("atomizer recognition is incomplete or empty", finding, StringComparison.Ordinal);
        Assert.Empty(result.Fallbacks);
        Assert.Empty(result.Residual);

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            ledger,
            snapshot,
            ledger));
        Assert.Contains(finding, exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestRetiresCoarseCasReceiptWhenARegisteredAdapterReplacesTheFallback()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**定理(观察者代数的唯一形态)。** claim。\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var coarseId = AtomId(coarse);
        var captured = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var baseline = Ledger(
            [],
            CasEntry("coarse-receipt", coarse, captured.Reference));
        var candidate = WithAtomizer(
            Ledger([], CasEntry("coarse-receipt", coarse, captured.Reference)),
            AtomizerRegistry.ObserverId);

        var plan = DigestionIngestor.Plan(
            candidate,
            Snapshot(sourceBytes, [captured]),
            baseline);
        var source = Assert.Single(plan.Document.RequireDigestionSources());
        var fine = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.ObserverId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);

        Assert.Equal(1, plan.StaleAcknowledged);
        Assert.Equal([coarseId], source.AcknowledgedStale.ToArray());
        Assert.Equal(
            captured.Reference,
            source.Entries.Single(entry => entry.AtomId == coarseId).CasRef);
        Assert.Contains(source.Entries, entry => entry.AtomId == AtomId(fine));

        var admitted = DigestionLedgerAligner.Evaluate(
            plan.Document,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(admitted.Findings);
        Assert.Empty(admitted.Residual);
        Assert.Equal(
            DigestionReceiptAlignment.Stale,
            admitted.AlignmentFor(coarseId));

        var migrated = plan.Document;
        var settled = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            migrated);

        Assert.Equal(0, settled.StaleAcknowledged);
        Assert.Equal(0, settled.ResidualOpenAdded);
        Assert.Equal(
            [coarseId],
            Assert.Single(settled.Document.RequireDigestionSources()).AcknowledgedStale.ToArray());
    }

    [Fact]
    public void IngestTreatsRegisteredLegacyFineReceiptAsAdapterReplacementIntent()
    {
        var (sourceBytes, coarseCapture, fineCapture, ledger) = MissedCoarseReplacement();
        var coarseId = coarseCapture.Reference["sha256:".Length..];
        var coarseBefore = Assert.Single(ledger.RequireDigestionEntries(), entry =>
            entry.AtomId == coarseId);

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, [coarseCapture, fineCapture]),
            ledger);
        var source = Assert.Single(plan.Document.RequireDigestionSources());
        var coarseAfter = Assert.Single(source.Entries, entry => entry.AtomId == coarseId);

        Assert.Equal(1, plan.StaleAcknowledged);
        Assert.Equal([coarseId], source.AcknowledgedStale.ToArray());
        Assert.Equal(coarseBefore.AtomId, coarseAfter.AtomId);
        Assert.Equal(coarseBefore.SourceId, coarseAfter.SourceId);
        Assert.Equal(coarseBefore.Fingerprints, coarseAfter.Fingerprints);
        Assert.Equal(coarseBefore.CasRef, coarseAfter.CasRef);
    }

    [Fact]
    public void AlignmentTreatsRegisteredLegacyFineReceiptAsAdapterReplacementIntent()
    {
        var (sourceBytes, coarseCapture, fineCapture, ledger) = MissedCoarseReplacement();
        var coarseId = coarseCapture.Reference["sha256:".Length..];

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes, [coarseCapture, fineCapture]),
            ledger,
            DigestionAlignmentMode.Ingest);

        Assert.Equal([coarseId], result.ActualStale.ToArray());
        Assert.Equal(DigestionReceiptAlignment.Stale, result.AlignmentFor(coarseId));
    }

    [Fact]
    public void AlignmentKeepsCoarseReceiptWhenRegisteredAdapterHasNoFineReceipt()
    {
        var (sourceBytes, coarseCapture, _, ledger) = MissedCoarseReplacement();
        var coarseId = coarseCapture.Reference["sha256:".Length..];
        var source = Assert.Single(ledger.RequireDigestionSources());
        var coarseOnly = ledger.WithDigestionSources(
            [source with
            {
                Entries = source.Entries
                    .Where(entry => entry.AtomId == coarseId)
                    .ToImmutableArray(),
            }]);

        var result = DigestionLedgerAligner.Evaluate(
            coarseOnly,
            Snapshot(sourceBytes, [coarseCapture]),
            coarseOnly,
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.ActualStale);
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(coarseId));
    }

    [Fact]
    public void IngestDoesNotRetireCoarseReceiptForFineReceiptWithoutRegisteredAdapter()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# Legacy\n\nfine claim\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var fineBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("fine claim"));
        var fineStart = sourceBytes.AsSpan().IndexOf(fineBytes.AsSpan());
        var fine = new DigestionAtom(
            fineStart,
            fineStart + fineBytes.Length,
            fineBytes,
            DigestionFingerprint.Compute(fineBytes.AsSpan()),
            []);
        var coarseCapture = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var fineCapture = DigestionCasStore.Capture(fineBytes.AsSpan());
        var ledger = WithAtomizer(
            Ledger(
                [],
                CasEntry("coarse-receipt", coarse, coarseCapture.Reference),
                CasEntry("fine-receipt", fine, fineCapture.Reference)),
            AtomizerRegistry.NoAtomizerId);

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, [coarseCapture, fineCapture]),
            ledger);

        Assert.Equal(0, plan.StaleAcknowledged);
        var source = Assert.Single(plan.Document.RequireDigestionSources());
        Assert.Empty(source.AcknowledgedStale);
        Assert.Contains(source.Entries, entry => entry.AtomId == AtomId(coarse));
        Assert.Contains(source.Entries, entry => entry.AtomId == AtomId(fine));
    }

    [Fact]
    public void IngestPreservesFineGenerationRetirementAcknowledgment()
    {
        var (sourceBytes, coarseCapture, fineCapture, ledger) = MissedCoarseReplacement();
        var snapshot = Snapshot(sourceBytes, [coarseCapture, fineCapture]);
        var first = DigestionIngestor.Plan(ledger, snapshot, ledger);
        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        using var temporary = new TemporaryDirectory();
        var persisted = new Dictionary<string, string>(StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(persisted, first.Document);
        DirectoryLedgerTestSupport.Write(temporary.Path, persisted);
        var settled = BackfillInventoryLoader.LoadRoot(temporary.Path);

        var second = DigestionIngestor.Plan(settled, snapshot, settled);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Equal(0, second.StaleAcknowledged);
        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Equal(firstBytes, secondBytes);
    }

    [Fact]
    public void DispositionDoesNotChangeSourceRevisionAdmissionOrRetirement()
    {
        var (sourceBytes, captured, plan, settled) = SettledCoarseReplacement();
        var coarseId = captured.Reference["sha256:".Length..];
        var source = Assert.Single(settled.RequireDigestionSources());
        var dispositioned = settled.WithDigestionSources(
        [
            source with
            {
                Entries = source.Entries.Select(entry => entry.AtomId == coarseId
                    ? entry with
                    {
                        Receipts = entry.Receipts with
                        {
                            CoverDisposition = new DigestionCoverDisposition(
                                new DigestionStatus(
                                    DigestionMigrationState.Partial,
                                    DigestionTruthState.Closed),
                                ["D5/S0/Synthetic/Receipt.coarse_generation"],
                                [new DigestionDispositionGap(
                                    "unresolved-subitem",
                                    "remaining coarse clause")],
                                new DateTimeOffset(
                                    2026,
                                    8,
                                    25,
                                    4,
                                    3,
                                    2,
                                    TestBudgets.ZeroDuration)),
                        },
                    }
                    : entry).ToImmutableArray(),
            },
        ]);
        var snapshot = Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects));

        var admitted = DigestionLedgerAligner.Evaluate(
            dispositioned,
            snapshot,
            settled,
            DigestionAlignmentMode.Admission);
        var replay = DigestionIngestor.Plan(dispositioned, snapshot, settled);

        Assert.Empty(admitted.Findings);
        Assert.Equal(DigestionReceiptAlignment.Stale, admitted.AlignmentFor(coarseId));
        Assert.Equal([coarseId], Assert.Single(replay.Document.RequireDigestionSources())
            .AcknowledgedStale.ToArray());
        Assert.Equal(0, replay.StaleAcknowledged);
        Assert.Equal(0, replay.ResidualOpenAdded);
    }

    [Fact]
    public void ProjectedStatusKeepsSettledStaleReceiptIdentityAndAlignmentByteIdempotent()
    {
        var (sourceBytes, captured, plan, settled) = SettledCoarseReplacement();
        var coarseId = captured.Reference["sha256:".Length..];
        var snapshot = Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects));
        var source = Assert.Single(settled.RequireDigestionSources());
        var projected = settled.WithDigestionSources(
        [
            source with
            {
                Entries = source.Entries.Select(entry => entry.AtomId == coarseId
                    ? entry with
                    {
                        ProjectedStatus = new DigestionStatus(
                            DigestionMigrationState.Partial,
                            DigestionTruthState.Closed),
                    }
                    : entry).ToImmutableArray(),
            },
        ]);

        var projectedAlignment = DigestionLedgerAligner.Evaluate(
            projected,
            snapshot,
            settled,
            DigestionAlignmentMode.Admission);
        var replay = DigestionIngestor.Plan(projected, snapshot, settled);
        var replayBytes = DirectoryLedgerTestSupport.Image(replay.Document);
        var secondReplay = DigestionIngestor.Plan(replay.Document, snapshot, settled);

        Assert.Empty(projectedAlignment.Findings);
        Assert.Equal(
            DigestionReceiptAlignment.Stale,
            projectedAlignment.AlignmentFor(coarseId));
        Assert.Empty(replay.Alignment.Findings);
        Assert.Equal(
            DigestionReceiptAlignment.Stale,
            replay.Alignment.AlignmentFor(coarseId));
        Assert.Equal(replayBytes, DirectoryLedgerTestSupport.Image(secondReplay.Document));
    }

    [Fact]
    public void IngestRetiresReplacedHistoricalCasAndRegistersEveryResidualOpenClaim()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n"
            + "**定理(观察者代数的唯一形态)。** first。\n\n"
            + "**定理(观察者代数的唯一形态)。** second。\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var coarseCapture = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var baseline = Ledger([], CasEntry("coarse", coarse, coarseCapture.Reference));
        var candidate = WithAtomizer(
            Ledger([], CasEntry("coarse", coarse, coarseCapture.Reference)),
            AtomizerRegistry.ObserverId);
        var fineAtoms = AtomizerRegistry.Atomize(
            AtomizerRegistry.ObserverId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims;

        var plan = DigestionIngestor.Plan(
            candidate,
            Snapshot(sourceBytes, [coarseCapture]),
            baseline);
        var source = Assert.Single(plan.Document.RequireDigestionSources());
        var coarseId = AtomId(coarse);
        var added = source.Entries.Where(entry => entry.AtomId != coarseId).ToArray();

        Assert.Equal([coarseId], source.AcknowledgedStale.ToArray());
        Assert.Equal(DigestionReceiptAlignment.Stale, plan.Alignment.AlignmentFor(coarseId));
        Assert.Equal(fineAtoms.Length, plan.ResidualOpenAdded);
        Assert.Equal(fineAtoms.Length, added.Length);
        Assert.All(added, entry =>
        {
            Assert.Equal(entry.Fingerprints.RawSha256["sha256:".Length..], entry.AtomId);
            Assert.Equal(entry.Fingerprints.RawSha256, entry.CasRef);
            Assert.Equal(
                new DigestionStatus(
                    DigestionMigrationState.Residual,
                    DigestionTruthState.Open),
                entry.ProjectedStatus);
        });
        Assert.Equal(
            fineAtoms.Select(AtomId).Order(StringComparer.Ordinal),
            added.Select(static entry => entry.AtomId).Order(StringComparer.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsRemovingASettledCoarseReplacementAcknowledgment()
    {
        var (sourceBytes, captured, plan, settled) = SettledCoarseReplacement();
        var coarseId = captured.Reference["sha256:".Length..];
        var settledSource = Assert.Single(settled.RequireDigestionSources());
        var revived = settled.WithDigestionSources(
        [
            settledSource with { AcknowledgedStale = [] },
        ]);

        var result = DigestionLedgerAligner.Evaluate(
            revived,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            settled,
            DigestionAlignmentMode.Admission);

        Assert.Equal(
            DigestionReceiptAlignment.Stale,
            result.AlignmentFor(coarseId));
        Assert.Contains(result.Findings, finding => finding.Contains(
            $"stale receipts are not acknowledged: {coarseId}",
            StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("atom-id")]
    [InlineData("fingerprints")]
    public void AdmissionRejectsMutatingASettledCoarseReplacementIdentity(string mutation)
    {
        var (sourceBytes, captured, plan, settled) = SettledCoarseReplacement();
        var coarseId = captured.Reference["sha256:".Length..];
        var source = Assert.Single(settled.RequireDigestionSources());
        var coarse = source.Entries.Single(entry => entry.AtomId == coarseId);
        var fine = source.Entries.Single(entry => entry.AtomId != coarseId);
        var mutated = mutation switch
        {
            "atom-id" => coarse with { AtomId = new string('0', 64) },
            "fingerprints" => coarse with { Fingerprints = fine.Fingerprints },
            _ => throw new ArgumentOutOfRangeException(nameof(mutation)),
        };
        var candidate = settled.WithDigestionSources(
            [source with
            {
                Entries = source.Entries
                    .Select(entry => entry.AtomId == coarseId ? mutated : entry)
                    .ToImmutableArray(),
            }]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            settled,
            DigestionAlignmentMode.Admission);

        Assert.Contains(result.Findings, finding => finding.Contains(
            $"content-wide replacement receipt identity changed or disappeared: {coarseId}",
            StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsCloningASettledCoarseReplacementReceipt()
    {
        var (sourceBytes, captured, plan, settled) = SettledCoarseReplacement();
        var coarseId = captured.Reference["sha256:".Length..];
        var source = Assert.Single(settled.RequireDigestionSources());
        var coarse = source.Entries.Single(entry => entry.AtomId == coarseId);
        var cloneId = new string('f', 64);
        var candidate = settled.WithDigestionSources(
            [source with
            {
                Entries = source.Entries.Add(coarse with { AtomId = cloneId }),
            }]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            settled,
            DigestionAlignmentMode.Admission);

        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(cloneId));
        Assert.Contains(result.Findings, finding => finding.Contains(
            $"new content-wide receipt after atomizer replacement: {cloneId}",
            StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsRenamingASettledCoarseReplacementSource()
    {
        var (sourceBytes, captured, plan, settled) = SettledCoarseReplacement();
        var source = Assert.Single(settled.RequireDigestionSources());
        const string renamedSourceId = "renamed-source";
        var candidate = settled.WithDigestionSources(
            [source with
            {
                SourceId = renamedSourceId,
                Entries = source.Entries
                    .Select(entry => entry with { SourceId = renamedSourceId })
                    .ToImmutableArray(),
            }]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            settled,
            DigestionAlignmentMode.Admission);

        Assert.Contains(result.Findings, finding => finding.Contains(
            "content-wide replacement source changed or disappeared: source",
            StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsDisablingASettledCoarseReplacementAtomizer()
    {
        var (sourceBytes, captured, plan, settled) = SettledCoarseReplacement();
        var source = Assert.Single(settled.RequireDigestionSources());
        var candidate = settled.WithDigestionSources(
            [source with
            {
                Atomizer = AtomizerRegistry.NoAtomizerId,
                AcknowledgedStale = [],
                Entries = source.Entries
                    .Select(entry => entry with { Atomizer = AtomizerRegistry.NoAtomizerId })
                    .ToImmutableArray(),
            }]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            settled,
            DigestionAlignmentMode.Admission);

        Assert.Contains(result.Findings, finding => finding.Contains(
            "settled content-wide replacement requires a registered atomizer: source",
            StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsRenamingTheSourceDuringInitialCoarseReplacement()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**定理(观察者代数的唯一形态)。** claim。\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var captured = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var baseline = Ledger(
            [],
            CasEntry("coarse-receipt", coarse, captured.Reference));
        var source = Assert.Single(baseline.RequireDigestionSources());
        const string renamedSourceId = "renamed-source";
        var candidate = baseline.WithDigestionSources(
            [source with
            {
                SourceId = renamedSourceId,
                Atomizer = AtomizerRegistry.ObserverId,
                Entries = source.Entries
                    .Select(entry => entry with
                    {
                        SourceId = renamedSourceId,
                        Atomizer = AtomizerRegistry.ObserverId,
                    })
                    .ToImmutableArray(),
            }]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, [captured]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(AtomId(coarse)));
        Assert.Contains(result.Findings, finding => finding.Contains(
            "content-wide replacement source changed or disappeared: source",
            StringComparison.Ordinal));
    }

    private static (
        byte[] SourceBytes,
        DigestionCasObject Captured,
        DigestionIngestPlan Plan,
        BackfillInventoryDocument Settled) SettledCoarseReplacement()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**定理(观察者代数的唯一形态)。** claim。\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var captured = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var original = Ledger(
            [],
            CasEntry("coarse-receipt", coarse, captured.Reference));
        var adapterCandidate = WithAtomizer(
            Ledger([], CasEntry("coarse-receipt", coarse, captured.Reference)),
            AtomizerRegistry.ObserverId);
        var plan = DigestionIngestor.Plan(
            adapterCandidate,
            Snapshot(sourceBytes, [captured]),
            original);
        var settled = plan.Document;
        return (sourceBytes, captured, plan, settled);
    }

    private static (
        byte[] SourceBytes,
        DigestionCasObject CoarseCapture,
        DigestionCasObject FineCapture,
        BackfillInventoryDocument Ledger) MissedCoarseReplacement()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**\u5b9a\u7406(\u89c2\u5bdf\u8005\u4ee3\u6570\u7684\u552f\u4e00\u5f62\u6001)\u3002** claim\u3002\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var fine = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.ObserverId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var coarseCapture = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var fineCapture = DigestionCasStore.Capture(fine.RawBytes.AsSpan());
        var ledger = WithAtomizer(
            Ledger(
                [],
                CasEntry("coarse-receipt", coarse, coarseCapture.Reference),
                CasEntry("fine-receipt", fine, fineCapture.Reference)),
            AtomizerRegistry.ObserverId);
        return (sourceBytes, coarseCapture, fineCapture, ledger);
    }
}
