using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void CasValidReceiptAbsentFromBaseAndCurrentSourceIsRejected()
    {
        var currentBytes = Encoding.UTF8.GetBytes("current live span");
        var currentAtom = Atom("claim/current", currentBytes);
        var forgedBytes = Encoding.UTF8.GetBytes("fabricated receipt bytes");
        var forgedAtom = new DigestionAtom(
            "theorem/does-not-exist",
            0,
            forgedBytes.Length,
            ImmutableArray.CreateRange(forgedBytes),
            DigestionFingerprint.Compute(forgedBytes),
            []);
        var forgedCapture = DigestionCasStore.Capture(forgedBytes);
        var baseline = BackfillInventoryLoader.Load(Ledger([], Entry("baseline-receipt", currentAtom)));
        var candidate = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("forged-receipt", forgedAtom, forgedCapture.Reference)));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [forgedCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(currentAtom));

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor("forged-receipt"));
        Assert.Null(result.AtomFor("forged-receipt"));
    }

    [Fact]
    public void CasValidReceiptWithExactBaseProvenanceIsInherited()
    {
        var oldBytes = Encoding.UTF8.GetBytes("historical span");
        var currentBytes = Encoding.UTF8.GetBytes("rewritten span");
        var oldAtom = Atom("claim/historical", oldBytes);
        var currentAtom = Atom("claim/historical", currentBytes);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("historical-receipt", oldAtom, oldCapture.Reference)));
        var candidate = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("historical-receipt", oldAtom, oldCapture.Reference)));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [oldCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(currentAtom));

        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor("historical-receipt"));
        Assert.Equal(oldAtom.Fingerprints, result.AtomFor("historical-receipt")?.Fingerprints);
    }

    [Fact]
    public void CasValidReceiptWithChangedAstPathIsNotInherited()
    {
        var oldBytes = Encoding.UTF8.GetBytes("historical span");
        var currentBytes = Encoding.UTF8.GetBytes("rewritten span");
        var oldAtom = Atom("claim/historical", oldBytes);
        var currentAtom = Atom("claim/historical", currentBytes);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("historical-receipt", oldAtom, oldCapture.Reference)));
        var candidateEntry = CasEntry("historical-receipt", oldAtom, oldCapture.Reference)
            .Replace("ast_path: claim/historical", "ast_path: claim/tampered", StringComparison.Ordinal);
        var candidate = BackfillInventoryLoader.Load(Ledger([], candidateEntry));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [oldCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(currentAtom));

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor("historical-receipt"));
        Assert.Null(result.AtomFor("historical-receipt"));
    }

    [Fact]
    public void CasValidReceiptMovedToAnotherSourceIsNotInherited()
    {
        var oldBytes = Encoding.UTF8.GetBytes("historical span");
        var currentBytes = Encoding.UTF8.GetBytes("rewritten span");
        var oldAtom = Atom("claim/historical", oldBytes);
        var currentAtom = Atom("claim/historical", currentBytes);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var entry = CasEntry("historical-receipt", oldAtom, oldCapture.Reference);
        var baseline = BackfillInventoryLoader.Load(Ledger([], entry));
        var candidate = BackfillInventoryLoader.Load(Ledger([], entry).Replace(
            "source_id: source",
            "source_id: moved-source",
            StringComparison.Ordinal));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [oldCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(currentAtom));

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor("historical-receipt"));
        Assert.Null(result.AtomFor("historical-receipt"));
    }

    [Fact]
    public void CasValidReceiptAbsentFromBaseIsAlignedByCurrentSourceSpan()
    {
        var currentBytes = Encoding.UTF8.GetBytes("current live span");
        var currentAtom = Atom("claim/current", currentBytes);
        var currentCapture = DigestionCasStore.Capture(currentAtom.RawBytes.AsSpan());
        var baselineBytes = Encoding.UTF8.GetBytes("baseline span");
        var baselineAtom = Atom("claim/baseline", baselineBytes);
        var baseline = BackfillInventoryLoader.Load(Ledger([], Entry("baseline-receipt", baselineAtom)));
        var candidate = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("live-receipt", currentAtom, currentCapture.Reference)));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [currentCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(currentAtom));

        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor("live-receipt"));
        Assert.Equal(currentAtom.Fingerprints, result.AtomFor("live-receipt")?.Fingerprints);
    }

    [Fact]
    public void IngestCarriesCoverageAndUnresolvedSubitemsForwardAcrossAtomGenerations()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# SYNTH-VOL\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# SYNTH-VOL\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(AtomizerRegistry.GictId, oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var loaded = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("old-receipt", oldAtom, oldCapture.Reference)));
        var source = Assert.Single(loaded.RequireDigestionSources());
        var oldEntry = Assert.Single(source.Entries) with
        {
            CoverageGids =
            [
                "D5/S3/Observer/WindowCharacter.window_algebra_has_no_character",
                "D5/S3/Quantum/QubitWitnesses.bell_coefficients_are_not_product",
            ],
            Receipts = Assert.Single(source.Entries).Receipts with
            {
                UnresolvedSubitems =
                [
                    "kochen-specker-projection-valuation-obstruction",
                    "hidden-address-local-variable-interpretation",
                    "classical-address-realism-exclusion",
                    "probability-not-ignorance-conclusion",
                ],
            },
        };
        var ledger = loaded.WithDigestionSources(
            [source with { Entries = [oldEntry] }]);

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(currentBytes, [oldCapture]),
            ledger);
        var nextGeneration = Assert.Single(
            Assert.Single(plan.Document.RequireDigestionSources()).Entries,
            static entry => entry.AtomId != "old-receipt");

        Assert.Empty(oldEntry.CoverageGids.Except(nextGeneration.CoverageGids, StringComparer.Ordinal));
        Assert.Empty(oldEntry.Receipts.UnresolvedSubitems.Except(
            nextGeneration.Receipts.UnresolvedSubitems,
            StringComparer.Ordinal));
    }

    [Fact]
    public void AdmissionAcceptsNestedChildrenOnlyWhenVerifiedParentListsExactPlan()
    {
        var parentBytes = Encoding.UTF8.GetBytes("abcdef");
        var parent = Atom("theorem/1.1", parentBytes);
        var first = SpannedAtom(parent, 0, 3, 1);
        var second = SpannedAtom(parent, 3, 6, 2);
        var parentCapture = DigestionCasStore.Capture(parentBytes);
        var firstCapture = DigestionCasStore.Capture(first.RawBytes.AsSpan());
        var secondCapture = DigestionCasStore.Capture(second.RawBytes.AsSpan());
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("parent", parent, parentCapture.Reference)));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var firstId = "gict-residual-" + firstCapture.Reference["sha256:".Length..];
        var secondId = "gict-residual-" + secondCapture.Reference["sha256:".Length..];
        var firstEntry = ChildEntry(parentEntry, firstId, first, firstCapture.Reference);
        var secondEntry = ChildEntry(parentEntry, secondId, second, secondCapture.Reference);
        var unchained = baseline.WithDigestionSources(
            [source with { Entries = [parentEntry, firstEntry, secondEntry] }]);
        var chained = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    parentEntry with
                    {
                        Receipts = parentEntry.Receipts with { ChainAtoms = [firstId, secondId] },
                        ReceiptSyntax = null,
                    },
                    firstEntry,
                    secondEntry,
                ],
            },
        ]);
        var snapshot = Snapshot(parentBytes, [parentCapture, firstCapture, secondCapture]);
        var atomized = new AtomizedTheoryDocument(
            [parent],
            [new DigestionSlice(true, parent.RawBytes)],
            [new DigestionClausePlan(parent.AstPath, [first, second])]);

        var rejected = DigestionLedgerAligner.Evaluate(
            unchained,
            snapshot,
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => atomized);
        var admitted = DigestionLedgerAligner.Evaluate(
            chained,
            snapshot,
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => atomized);
        var inheritedButUnchained = DigestionLedgerAligner.Evaluate(
            unchained,
            snapshot,
            chained,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => atomized);

        Assert.All([firstId, secondId], childId => Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            rejected.AlignmentFor(childId)));
        Assert.All([firstId, secondId], childId => Assert.Equal(
            DigestionReceiptAlignment.Seen,
            admitted.AlignmentFor(childId)));
        Assert.Equal(first.Fingerprints, admitted.AtomFor(firstId)?.Fingerprints);
        Assert.Equal(second.Fingerprints, admitted.AtomFor(secondId)?.Fingerprints);
        Assert.All([firstId, secondId], childId => Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            inheritedButUnchained.AlignmentFor(childId)));
    }

    [Fact]
    public void AdmissionRejectsLedgerAuthoredSubsetOfRecomputedClausePlan()
    {
        var parentBytes = Encoding.UTF8.GetBytes("abcdef");
        var parent = Atom("theorem/1.1", parentBytes);
        var first = SpannedAtom(parent, 0, 3, 1);
        var second = SpannedAtom(parent, 3, 6, 2);
        var parentCapture = DigestionCasStore.Capture(parent.RawBytes.AsSpan());
        var firstCapture = DigestionCasStore.Capture(first.RawBytes.AsSpan());
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("parent", parent, parentCapture.Reference)));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var firstId = "gict-residual-" + firstCapture.Reference["sha256:".Length..];
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    parentEntry with
                    {
                        Receipts = parentEntry.Receipts with { ChainAtoms = [firstId] },
                        ReceiptSyntax = null,
                    },
                    ChildEntry(parentEntry, firstId, first, firstCapture.Reference),
                ],
            },
        ]);
        var atomized = new AtomizedTheoryDocument(
            [parent],
            [new DigestionSlice(true, parent.RawBytes)],
            [new DigestionClausePlan(parent.AstPath, [first, second])]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(parentBytes, [parentCapture, firstCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => atomized);

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(firstId));
        Assert.Null(result.AtomFor(firstId));
    }

    [Fact]
    public void EvaluatorDoesNotTreatLedgerAuthoredClauseSubsetAsVerifiedAbsorptionChain()
    {
        const string claim = """
            **定理 18.7(链验证)**。first clause。

            **推论:第二子句**;the full plan has two clauses。

            """;
        var sourceBytes = Encoding.UTF8.GetBytes("# PZG\n\n" + claim);
        var atomized = PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var parent = Assert.Single(atomized.Claims);
        var plan = Assert.Single(atomized.ClausePlans);
        var first = plan.Children[0];
        var parentCapture = DigestionCasStore.Capture(parent.RawBytes.AsSpan());
        var firstCapture = DigestionCasStore.Capture(first.RawBytes.AsSpan());
        var baseline = BackfillInventoryLoader.Load(
            Ledger([], CasEntry("parent", parent, parentCapture.Reference))
                .Replace(AtomizerRegistry.GictId, AtomizerRegistry.PzgId, StringComparison.Ordinal));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var firstId = "pzg-residual-" + firstCapture.Reference["sha256:".Length..];
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var target = Encoding.UTF8.GetBytes(DigestionTestSupport.Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var targetHash = DigestionFingerprint.Compute(target).RawSha256;
        DigestionLedgerEntry Complete(
            DigestionLedgerEntry template,
            string atomId,
            DigestionAtom atom,
            ImmutableArray<string> chainAtoms) => template with
        {
            AtomId = atomId,
            AstPath = atom.AstPath,
            Boundary = null,
            Fingerprints = atom.Fingerprints,
            CoverageGids = [gid],
            Receipts = new DigestionReceipts(
                [new DigestionCoverageReceipt(gid, atom.Fingerprints.RawSha256, targetHash)],
                [new DigestionScribeReceipt(gid, definitionHash, emissionHash)],
                [],
                chainAtoms,
                null),
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
            ReceiptSyntax = null,
            CasRef = atom.Fingerprints.RawSha256,
        };
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    Complete(parentEntry, "parent", parent, [firstId]),
                    Complete(parentEntry, firstId, first, []),
                ],
            },
        ]);
        var record = new ScribeEmissionRecord(
            gid,
            ScribeEmissionAttestation.DefinitionPath(gid),
            definitionHash,
            ScribeEmissionAttestation.EmissionPath(gid),
            emissionHash);
        var snapshot = DigestionTestSupport.Snapshot(
            ("docs/source.md", sourceBytes),
            DigestionTestSupport.CasFile(parent),
            DigestionTestSupport.CasFile(first),
            (targetPath, target),
            (record.DefinitionPath, definition),
            (record.EmissionPath, emission));

        var evaluation = DigestionStatusEvaluator.Evaluate(
            candidate,
            snapshot,
            DigestionTestSupport.AcceptedLean(targetPath),
            VerifiedScribeEmissions.Create([record]),
            baselineDocument: baseline);

        var evaluatedParent = Assert.Single(
            evaluation.Entries,
            static entry => entry.Entry.AtomId == "parent");
        Assert.NotEqual(DigestionMigrationState.Absorbed, evaluatedParent.DerivedStatus.Migration);
        Assert.Contains(evaluation.Findings, finding => finding.Contains(
            "entry parent handwritten status",
            StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRollsBackValidSiblingWhenAnotherSiblingIsInvalid()
    {
        var parentBytes = Encoding.UTF8.GetBytes("abcdef");
        var parent = Atom("theorem/1.1", parentBytes);
        var first = SpannedAtom(parent, 0, 3, 1);
        var plannedSecond = SpannedAtom(parent, 3, 6, 2);
        var invalidSecond = Atom("theorem/1.1/clause/2", Encoding.UTF8.GetBytes("xyz"));
        var parentCapture = DigestionCasStore.Capture(parent.RawBytes.AsSpan());
        var firstCapture = DigestionCasStore.Capture(first.RawBytes.AsSpan());
        var invalidCapture = DigestionCasStore.Capture(invalidSecond.RawBytes.AsSpan());
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("parent", parent, parentCapture.Reference)));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var firstId = "gict-residual-" + firstCapture.Reference["sha256:".Length..];
        var invalidId = "gict-residual-" + invalidCapture.Reference["sha256:".Length..];
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    parentEntry with
                    {
                        Receipts = parentEntry.Receipts with { ChainAtoms = [firstId, invalidId] },
                        ReceiptSyntax = null,
                    },
                    ChildEntry(parentEntry, firstId, first, firstCapture.Reference),
                    ChildEntry(parentEntry, invalidId, invalidSecond, invalidCapture.Reference),
                ],
            },
        ]);
        var atomized = new AtomizedTheoryDocument(
            [parent],
            [new DigestionSlice(true, parent.RawBytes)],
            [new DigestionClausePlan(parent.AstPath, [first, plannedSecond])]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(parentBytes, [parentCapture, firstCapture, invalidCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => atomized);

        Assert.All([firstId, invalidId], childId => Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(childId)));
        Assert.Null(result.AtomFor(firstId));
        Assert.Null(result.AtomFor(invalidId));
    }

    [Theory]
    [InlineData("outside")]
    [InlineData("non-unique")]
    [InlineData("overlap")]
    public void AdmissionRejectsUnverifiedNestedChildSpans(string defect)
    {
        var parentBytes = Encoding.UTF8.GetBytes(defect == "non-unique" ? "abcabc" : "abcdef");
        var childByteSets = defect switch
        {
            "outside" => new[] { Encoding.UTF8.GetBytes("xyz") },
            "non-unique" => new[] { Encoding.UTF8.GetBytes("abc") },
            "overlap" => new[] { Encoding.UTF8.GetBytes("abcd"), Encoding.UTF8.GetBytes("cdef") },
            _ => throw new ArgumentOutOfRangeException(nameof(defect)),
        };
        var parent = Atom("theorem/1.1", parentBytes);
        var parentCapture = DigestionCasStore.Capture(parentBytes);
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("parent", parent, parentCapture.Reference)));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var childCaptures = childByteSets
            .Select(static bytes => DigestionCasStore.Capture(bytes))
            .ToArray();
        var children = childByteSets.Select((bytes, index) =>
            Atom($"theorem/1.1/clause/{index + 1}", bytes)).ToArray();
        var childIds = childCaptures.Select(static capture =>
            "gict-residual-" + capture.Reference["sha256:".Length..]).ToImmutableArray();
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    parentEntry with
                    {
                        Receipts = parentEntry.Receipts with { ChainAtoms = childIds },
                        ReceiptSyntax = null,
                    },
                    .. children.Select((child, index) => ChildEntry(
                        parentEntry,
                        childIds[index],
                        child,
                        childCaptures[index].Reference)),
                ],
            },
        ]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(parentBytes, childCaptures.Prepend(parentCapture)),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(parent));

        Assert.All(childIds, childId => Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(childId)));
    }

    [Fact]
    public void IngestRejectsOverlappingClausePlanBoundaries()
    {
        var parentBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("abcdef"));
        var parent = new DigestionAtom(
            "theorem/1.1",
            0,
            parentBytes.Length,
            parentBytes,
            DigestionFingerprint.Compute(parentBytes.AsSpan()),
            []);
        var firstBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("abcd"));
        var secondBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("cdef"));
        var first = new DigestionAtom(
            "theorem/1.1/clause/1",
            0,
            4,
            firstBytes,
            DigestionFingerprint.Compute(firstBytes.AsSpan()),
            []);
        var second = new DigestionAtom(
            "theorem/1.1/clause/2",
            2,
            6,
            secondBytes,
            DigestionFingerprint.Compute(secondBytes.AsSpan()),
            []);
        var invalid = new AtomizedTheoryDocument(
            [parent],
            [new DigestionSlice(true, parentBytes)],
            [new DigestionClausePlan(parent.AstPath, [first, second])]);
        var captured = DigestionCasStore.Capture(parentBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("parent", parent, captured.Reference)));

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(parentBytes.ToArray(), [captured]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => invalid);

        Assert.Contains(result.Findings, finding => finding.Contains(
            "clause plan",
            StringComparison.Ordinal));
    }

    [Theory]
    [InlineData(1, 3, 3, 6)]
    [InlineData(0, 2, 3, 6)]
    [InlineData(0, 3, 3, 5)]
    public void IngestRejectsClausePlanThatDoesNotTileParent(
        int firstStart,
        int firstEnd,
        int secondStart,
        int secondEnd)
    {
        var parentBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("abcdef"));
        var parent = new DigestionAtom(
            "theorem/1.1",
            0,
            parentBytes.Length,
            parentBytes,
            DigestionFingerprint.Compute(parentBytes.AsSpan()),
            []);
        var first = SpannedAtom(parent, firstStart, firstEnd, 1);
        var second = SpannedAtom(parent, secondStart, secondEnd, 2);
        var invalid = new AtomizedTheoryDocument(
            [parent],
            [new DigestionSlice(true, parentBytes)],
            [new DigestionClausePlan(parent.AstPath, [first, second])]);
        var captured = DigestionCasStore.Capture(parentBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("parent", parent, captured.Reference)));

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(parentBytes.ToArray(), [captured]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => invalid);

        Assert.Contains(result.Findings, finding => finding.Contains(
            "do not tile",
            StringComparison.Ordinal));
    }

    private static DigestionAtom Atom(string astPath, byte[] bytes) => new(
        astPath,
        0,
        bytes.Length,
        ImmutableArray.CreateRange(bytes),
        DigestionFingerprint.Compute(bytes),
        []);

    private static DigestionAtom SpannedAtom(
        DigestionAtom parent,
        int start,
        int end,
        int clause) => new(
            $"{parent.AstPath}/clause/{clause}",
            parent.StartByte + start,
            parent.StartByte + end,
            parent.RawBytes[start..end],
            DigestionFingerprint.Compute(parent.RawBytes.AsSpan()[start..end]),
            parent.Context);

    private static AtomizedTheoryDocument Atomized(DigestionAtom atom) => new(
        [atom],
        [new DigestionSlice(true, atom.RawBytes)]);

    private static DigestionLedgerEntry ChildEntry(
        DigestionLedgerEntry parent,
        string atomId,
        DigestionAtom child,
        string casRef) => parent with
        {
            AtomId = atomId,
            AstPath = child.AstPath,
            Boundary = null,
            Fingerprints = child.Fingerprints,
            CoverageGids = [],
            Receipts = new DigestionReceipts([], [], [], [], null),
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Residual,
                DigestionTruthState.Open),
            ReceiptSyntax = null,
            CasRef = casRef,
        };

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
            [new DigestionSlice(true, sourceBytes)]);

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
            [new DigestionSlice(true, sourceBytes)]);

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
            [new DigestionSlice(false, ImmutableArray.Create((byte)'b'))]);

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
    public void IngestFallsBackWhenZeroClaimAtomizerOutputExactlyReassemblesTheSource()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var unrecognized = new AtomizedTheoryDocument(
            [],
            [new DigestionSlice(false, sourceBytes)]);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [oldCapture]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => unrecognized);

        Assert.Empty(result.Findings);
        Assert.Single(result.Fallbacks);
        Assert.Equal(sourceBytes.ToArray(), Assert.Single(result.Residual).Atom.RawBytes.ToArray());
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
        var unrecognized = new AtomizedTheoryDocument(
            [],
            [new DigestionSlice(false, sourceBytes)]);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [captured]),
            ledger,
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
            [new DigestionSlice(true, atomBytes), new DigestionSlice(true, atomBytes)]);

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
}
