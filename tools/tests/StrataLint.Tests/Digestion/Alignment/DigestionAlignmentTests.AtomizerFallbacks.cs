using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void IngestRejectsAtomizerHashFailureInsteadOfFallingBack()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var corrupt = new DigestionAtom(
            "theorem/1.2",
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
            "theorem/1.2",
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
    public void CoarseFallbackDoesNotCollapseASeparateOccurrenceWithIdenticalBytes()
    {
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var fingerprints = DigestionFingerprint.Compute(sourceBytes.AsSpan());
        var existing = new DigestionAtom(
            "theorem/1.1",
            0,
            sourceBytes.Length,
            sourceBytes,
            fingerprints,
            []);
        var captured = DigestionCasStore.Capture(sourceBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("existing-receipt", existing, captured.Reference)));
        var baseline = BackfillInventoryLoader.Load(Ledger([]));
        var unrecognized = new AtomizedTheoryDocument(
            [],
            [new DigestionSlice(false, sourceBytes)],
            GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [captured]),
            baseline,
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => unrecognized);

        Assert.Empty(result.Findings);
        Assert.Single(result.Fallbacks);
        Assert.Equal("coarse/source", Assert.Single(result.Residual).Atom.AstPath);
    }

    [Fact]
    public void CasReceiptSubtractsOnlyItsRecordedOccurrenceWhenRawBytesRepeat()
    {
        var atomBytes = ImmutableArray.Create((byte)'a');
        var fingerprints = DigestionFingerprint.Compute(atomBytes.AsSpan());
        var first = new DigestionAtom("theorem/1.1", 0, 1, atomBytes, fingerprints, []);
        var second = new DigestionAtom("theorem/1.2", 1, 2, atomBytes, fingerprints, []);
        var captured = DigestionCasStore.Capture(atomBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("first-receipt", first, captured.Reference)));
        var atomized = new AtomizedTheoryDocument(
            [first, second],
            [new DigestionSlice(true, atomBytes), new DigestionSlice(true, atomBytes)],
            GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot([(byte)'a', (byte)'a'], [captured]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => atomized);

        Assert.Empty(result.Findings);
        Assert.Equal("theorem/1.2", Assert.Single(result.Residual).Atom.AstPath);
    }

    [Fact]
    public void IngestRetiresCoarseCasReceiptWhenARegisteredAdapterReplacesTheFallback()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**定理(观察者代数的唯一形态)。** claim。\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            "coarse/source",
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var captured = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var priorAtomizer = SyntheticNumberedAtomizer.Id;
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("coarse-receipt", coarse, captured.Reference)));
        var candidate = BackfillInventoryLoader.Load(
            Ledger([], CasEntry("coarse-receipt", coarse, captured.Reference))
                .Replace(
                    $"atomizer: {priorAtomizer}",
                    $"atomizer: {AtomizerRegistry.ObserverId}",
                    StringComparison.Ordinal));

        var plan = DigestionIngestor.Plan(
            candidate,
            Snapshot(sourceBytes, [captured]),
            baseline);
        var source = Assert.Single(plan.Document.RequireDigestionSources());

        Assert.Equal(1, plan.StaleAcknowledged);
        Assert.Equal(["coarse-receipt"], source.AcknowledgedStale.ToArray());
        Assert.Equal(
            captured.Reference,
            source.Entries.Single(static entry => entry.AtomId == "coarse-receipt").CasRef);
        Assert.Equal(
            "theorem/observer-algebra",
            source.Entries.Single(static entry => entry.AtomId != "coarse-receipt").AstPath);

        var admitted = DigestionLedgerAligner.Evaluate(
            plan.Document,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(admitted.Findings);
        Assert.Empty(admitted.Residual);
        Assert.Equal(
            DigestionReceiptAlignment.Stale,
            admitted.AlignmentFor("coarse-receipt"));

        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(
            BackfillInventoryWriter.WriteForIngest(plan.Document).AsSpan()));
        var settled = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            migrated);

        Assert.Equal(0, settled.StaleAcknowledged);
        Assert.Equal(0, settled.ResidualOpenAdded);
        Assert.Equal(
            ["coarse-receipt"],
            Assert.Single(settled.Document.RequireDigestionSources()).AcknowledgedStale.ToArray());
    }

    [Fact]
    public void IngestRepairsMissedCoarseRetirementAfterAdapterFineReceiptsExist()
    {
        var (sourceBytes, coarseCapture, fineCapture, ledger) = MissedCoarseReplacement();
        var coarseBefore = Assert.Single(ledger.RequireDigestionEntries(), static entry =>
            entry.AtomId == "coarse-receipt");

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, [coarseCapture, fineCapture]),
            ledger);
        var source = Assert.Single(plan.Document.RequireDigestionSources());
        var coarseAfter = Assert.Single(source.Entries, static entry =>
            entry.AtomId == "coarse-receipt");

        Assert.Equal(1, plan.StaleAcknowledged);
        Assert.Equal(["coarse-receipt"], source.AcknowledgedStale.ToArray());
        Assert.Equal(coarseBefore.AtomId, coarseAfter.AtomId);
        Assert.Equal(coarseBefore.AstPath, coarseAfter.AstPath);
        Assert.Equal(coarseBefore.Fingerprints, coarseAfter.Fingerprints);
        Assert.Equal(coarseBefore.CasRef, coarseAfter.CasRef);
    }

    [Fact]
    public void IngestDoesNotRetireCoarseReceiptForFineLegacyBoundariesWithoutAdapter()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# Legacy\n\nfine claim\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            "coarse/source",
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var fineBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("fine claim"));
        var fineStart = sourceBytes.AsSpan().IndexOf(fineBytes.AsSpan());
        var fine = new DigestionAtom(
            "legacy/fine",
            fineStart,
            fineStart + fineBytes.Length,
            fineBytes,
            DigestionFingerprint.Compute(fineBytes.AsSpan()),
            []);
        var coarseCapture = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var fineCapture = DigestionCasStore.Capture(fineBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(
            Ledger(
                    [],
                    LegacyEntry("coarse-receipt", coarse),
                    LegacyEntry("fine-receipt", fine))
                .Replace(
                    $"atomizer: {AtomizerRegistry.GictId}",
                    $"atomizer: {AtomizerRegistry.NoAtomizerId}",
                    StringComparison.Ordinal));

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, [coarseCapture, fineCapture]),
            ledger);

        Assert.Equal(0, plan.StaleAcknowledged);
        var source = Assert.Single(plan.Document.RequireDigestionSources());
        Assert.Empty(source.AcknowledgedStale);
        Assert.Contains(source.Entries, static entry => entry.AstPath == "coarse/source");
        Assert.Contains(source.Entries, static entry => entry.AstPath == "legacy/fine");
    }

    [Fact]
    public void RepairedCoarseRetirementIsIdempotentAcrossConsecutiveIngests()
    {
        var (sourceBytes, coarseCapture, fineCapture, ledger) = MissedCoarseReplacement();
        var snapshot = Snapshot(sourceBytes, [coarseCapture, fineCapture]);
        var first = DigestionIngestor.Plan(ledger, snapshot, ledger);
        var firstBytes = BackfillInventoryWriter.WriteForIngest(first.Document);
        var settled = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));

        var second = DigestionIngestor.Plan(settled, snapshot, settled);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Equal(0, second.StaleAcknowledged);
        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }

    [Fact]
    public void AdmissionRejectsRemovingASettledCoarseReplacementAcknowledgment()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**定理(观察者代数的唯一形态)。** claim。\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            "coarse/source",
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var captured = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var priorAtomizer = SyntheticNumberedAtomizer.Id;
        var original = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("coarse-receipt", coarse, captured.Reference)));
        var adapterCandidate = BackfillInventoryLoader.Load(
            Ledger([], CasEntry("coarse-receipt", coarse, captured.Reference))
                .Replace(
                    $"atomizer: {priorAtomizer}",
                    $"atomizer: {AtomizerRegistry.ObserverId}",
                    StringComparison.Ordinal));
        var plan = DigestionIngestor.Plan(
            adapterCandidate,
            Snapshot(sourceBytes, [captured]),
            original);
        var settledBytes = Encoding.UTF8.GetString(
            BackfillInventoryWriter.WriteForIngest(plan.Document).AsSpan());
        var settled = BackfillInventoryLoader.Load(settledBytes);
        var revived = BackfillInventoryLoader.Load(settledBytes.Replace(
            "    acknowledged_stale:\n      - coarse-receipt\n",
            "    acknowledged_stale: []\n",
            StringComparison.Ordinal));

        var result = DigestionLedgerAligner.Evaluate(
            revived,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            settled,
            DigestionAlignmentMode.Admission);

        Assert.Equal(
            DigestionReceiptAlignment.Stale,
            result.AlignmentFor("coarse-receipt"));
        Assert.Contains(result.Findings, finding => finding.Contains(
            "stale receipts are not acknowledged: coarse-receipt",
            StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("ast-path")]
    [InlineData("atom-id")]
    [InlineData("fingerprints")]
    public void AdmissionRejectsMutatingASettledCoarseReplacementIdentity(string mutation)
    {
        var (sourceBytes, captured, plan, settled) = SettledCoarseReplacement();
        var source = Assert.Single(settled.RequireDigestionSources());
        var coarse = source.Entries.Single(static entry => entry.AtomId == "coarse-receipt");
        var fine = source.Entries.Single(static entry => entry.AtomId != "coarse-receipt");
        var mutated = mutation switch
        {
            "ast-path" => coarse with { AstPath = "coarse/renamed" },
            "atom-id" => coarse with { AtomId = "renamed-coarse" },
            "fingerprints" => coarse with
            {
                Fingerprints = coarse.Fingerprints with
                {
                    NormalizedSha256 = fine.Fingerprints.NormalizedSha256,
                },
            },
            _ => throw new ArgumentOutOfRangeException(nameof(mutation)),
        };
        var candidate = settled.WithDigestionSources(
            [source with
            {
                Entries = source.Entries
                    .Select(entry => entry.AtomId == "coarse-receipt" ? mutated : entry)
                    .ToImmutableArray(),
            }]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            settled,
            DigestionAlignmentMode.Admission);

        Assert.Contains(result.Findings, finding => finding.Contains(
            "coarse replacement receipt identity changed or disappeared: coarse-receipt",
            StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("coarse/source")]
    [InlineData("coarse/renamed")]
    public void AdmissionRejectsCloningASettledCoarseReplacementReceipt(string astPath)
    {
        var (sourceBytes, captured, plan, settled) = SettledCoarseReplacement();
        var source = Assert.Single(settled.RequireDigestionSources());
        var coarse = source.Entries.Single(static entry => entry.AtomId == "coarse-receipt");
        var candidate = settled.WithDigestionSources(
            [source with
            {
                Entries = source.Entries.Add(coarse with
                {
                    AtomId = "coarse-clone",
                    AstPath = astPath,
                }),
            }]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            settled,
            DigestionAlignmentMode.Admission);

        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor("coarse-clone"));
        Assert.Contains(result.Findings, finding => finding.Contains(
            "new coarse receipt after fine atomization: coarse-clone",
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
            "coarse replacement source changed or disappeared: source",
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
            "settled coarse replacement requires a registered atomizer: source",
            StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsRenamingTheSourceDuringInitialCoarseReplacement()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**定理(观察者代数的唯一形态)。** claim。\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            "coarse/source",
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var captured = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("coarse-receipt", coarse, captured.Reference)));
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
            result.AlignmentFor("coarse-receipt"));
        Assert.Contains(result.Findings, finding => finding.Contains(
            "coarse replacement source changed or disappeared: source",
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
            "coarse/source",
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var captured = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var priorAtomizer = SyntheticNumberedAtomizer.Id;
        var original = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("coarse-receipt", coarse, captured.Reference)));
        var adapterCandidate = BackfillInventoryLoader.Load(
            Ledger([], CasEntry("coarse-receipt", coarse, captured.Reference))
                .Replace(
                    $"atomizer: {priorAtomizer}",
                    $"atomizer: {AtomizerRegistry.ObserverId}",
                    StringComparison.Ordinal));
        var plan = DigestionIngestor.Plan(
            adapterCandidate,
            Snapshot(sourceBytes, [captured]),
            original);
        var settled = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(
            BackfillInventoryWriter.WriteForIngest(plan.Document).AsSpan()));
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
            "coarse/source",
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
        var ledger = BackfillInventoryLoader.Load(
            Ledger(
                    [],
                    CasEntry("coarse-receipt", coarse, coarseCapture.Reference),
                    CasEntry("fine-receipt", fine, fineCapture.Reference))
                .Replace(
                    $"atomizer: {AtomizerRegistry.GictId}",
                    $"atomizer: {AtomizerRegistry.ObserverId}",
                    StringComparison.Ordinal));
        return (sourceBytes, coarseCapture, fineCapture, ledger);
    }
}
