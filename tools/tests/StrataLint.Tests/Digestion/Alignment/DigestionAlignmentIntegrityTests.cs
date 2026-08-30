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
            0,
            forgedBytes.Length,
            ImmutableArray.CreateRange(forgedBytes),
            DigestionFingerprint.Compute(forgedBytes),
            []);
        var forgedCapture = DigestionCasStore.Capture(forgedBytes);
        var baseline = Ledger([], Entry("baseline-receipt", currentAtom));
        var candidate = Ledger(
            [],
            CasEntry("forged-receipt", forgedAtom, forgedCapture.Reference));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [forgedCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(currentAtom));

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(forgedAtom)));
        Assert.Equal(forgedAtom.Fingerprints, result.AtomFor(AtomId(forgedAtom))?.Fingerprints);
    }

    [Fact]
    public void CasValidReceiptWithExactBaseProvenanceIsInherited()
    {
        var oldBytes = Encoding.UTF8.GetBytes("historical span");
        var currentBytes = Encoding.UTF8.GetBytes("rewritten span");
        var oldAtom = Atom("claim/historical", oldBytes);
        var currentAtom = Atom("claim/historical", currentBytes);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var baseline = Ledger(
            [],
            CasEntry("historical-receipt", oldAtom, oldCapture.Reference));
        var candidate = Ledger(
            [],
            CasEntry("historical-receipt", oldAtom, oldCapture.Reference));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [oldCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(currentAtom));

        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(AtomId(oldAtom)));
        Assert.Equal(oldAtom.Fingerprints, result.AtomFor(AtomId(oldAtom))?.Fingerprints);
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
        var baseline = Ledger([], entry);
        var candidate = WithSourceId(Ledger([], entry), "moved-source");

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [oldCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(currentAtom));

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(oldAtom)));
        Assert.Equal(oldAtom.Fingerprints, result.AtomFor(AtomId(oldAtom))?.Fingerprints);
    }

    [Fact]
    public void CasValidReceiptAbsentFromBaseIsAlignedByCurrentSourceSpan()
    {
        var currentBytes = Encoding.UTF8.GetBytes("current live span");
        var currentAtom = Atom("claim/current", currentBytes);
        var currentCapture = DigestionCasStore.Capture(currentAtom.RawBytes.AsSpan());
        var baselineBytes = Encoding.UTF8.GetBytes("baseline span");
        var baselineAtom = Atom("claim/baseline", baselineBytes);
        var baseline = Ledger([], Entry("baseline-receipt", baselineAtom));
        var candidate = Ledger(
            [],
            CasEntry("live-receipt", currentAtom, currentCapture.Reference));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [currentCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(currentAtom));

        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(AtomId(currentAtom)));
        Assert.Equal(currentAtom.Fingerprints, result.AtomFor(AtomId(currentAtom))?.Fingerprints);
    }

    [Fact]
    public void AdmissionVerifiesRecordedClauseChainFromParentCasAndPreservesInheritedAlignment()
    {
        const string claim = """
            **定理 18.7(Parent)**. first clause.

            **推论:Second clause**. second clause.

            """;
        var sourceBytes = Encoding.UTF8.GetBytes("# PZG\n\n" + claim);
        var atomized = PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var parent = Assert.Single(atomized.Claims);
        var clausePlan = Assert.Single(atomized.ClausePlans);
        Assert.Equal(2, clausePlan.Children.Length);
        var first = clausePlan.Children[0];
        var second = clausePlan.Children[1];
        var parentCapture = DigestionCasStore.Capture(parent.RawBytes.AsSpan());
        var firstCapture = DigestionCasStore.Capture(first.RawBytes.AsSpan());
        var secondCapture = DigestionCasStore.Capture(second.RawBytes.AsSpan());
        var baseline = Ledger(
            [],
            CasEntry("parent", parent, parentCapture.Reference));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var firstId = firstCapture.Reference["sha256:".Length..];
        var secondId = secondCapture.Reference["sha256:".Length..];
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
                    },
                    firstEntry,
                    secondEntry,
                ],
            },
        ]);
        var snapshot = Snapshot(sourceBytes, [parentCapture, firstCapture, secondCapture]);

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
        Assert.All([firstId, secondId], childId => Assert.Null(inheritedButUnchained.AtomFor(childId)));
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
        var baseline = Ledger(
            [],
            CasEntry("parent", parent, parentCapture.Reference));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var firstId = firstCapture.Reference["sha256:".Length..];
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    parentEntry with
                    {
                        Receipts = parentEntry.Receipts with { ChainAtoms = [firstId] },
                    },
                    ChildEntry(parentEntry, firstId, first, firstCapture.Reference),
                ],
            },
        ]);
        var atomized = new AtomizedTheoryDocument(
            [parent],
            [new DigestionSlice(true, parent.RawBytes)],
            [new DigestionClausePlan(parent, [first, second])],
            GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(parentBytes, [parentCapture, firstCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => atomized);

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(firstId));
        Assert.Null(result.AtomFor(firstId));
        Assert.Contains(result.Findings, finding => finding.Contains(
            $"entry {parentEntry.AtomId} malformed clause chain",
            StringComparison.Ordinal));
    }

    [Fact]
    public void CurrentFrontierRejectsInheritedStandaloneClausePlanChild()
    {
        var parentBytes = Encoding.UTF8.GetBytes("abcdef");
        var parent = Atom("theorem/1.1", parentBytes);
        var first = SpannedAtom(parent, 0, 3, 1);
        var second = SpannedAtom(parent, 3, 6, 2);
        var probe = Atom("theorem/probe", Encoding.UTF8.GetBytes("probe"));
        var parentCapture = DigestionCasStore.Capture(parent.RawBytes.AsSpan());
        var firstCapture = DigestionCasStore.Capture(first.RawBytes.AsSpan());
        var probeCapture = DigestionCasStore.Capture(probe.RawBytes.AsSpan());
        var baselineParent = CasEntry("parent", parent, parentCapture.Reference);
        var baselineChild = ChildEntry(
            baselineParent,
            AtomId(first),
            first,
            firstCapture.Reference);
        var baseline = Ledger([], baselineParent, baselineChild);
        var source = Assert.Single(baseline.RequireDigestionSources());
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    .. source.Entries,
                    CasEntry("unproven-probe", probe, probeCapture.Reference),
                ],
            },
        ]);
        var atomized = new AtomizedTheoryDocument(
            [parent],
            [new DigestionSlice(true, parent.RawBytes)],
            [new DigestionClausePlan(parent, [first, second])],
            GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(parentBytes, [parentCapture, firstCapture, probeCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => atomized);

        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(baselineChild.AtomId));
        Assert.Null(result.AtomFor(baselineChild.AtomId));
    }

    [Fact]
    public void Sl016PublishesMalformedAuthoredClauseChainFinding()
    {
        var (sourceBytes, _, candidate, parentCapture, childCapture) = MalformedPzgClauseSubset();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Files[parentCapture.RelativePath] = Encoding.UTF8.GetString(parentCapture.Bytes.AsSpan());
        fixture.Files[childCapture.RelativePath] = Encoding.UTF8.GetString(childCapture.Bytes.AsSpan());
        var candidateSource = Assert.Single(candidate.RequireDigestionSources());
        DirectoryLedgerTestSupport.ReplaceWithProjection(
            fixture.Files,
            candidate.WithDigestionSources(
            [
                candidateSource with
                {
                    SourcePath = RuleFixture.FixtureDigestionSourcePath,
                    Entries = candidateSource.Entries.Select(entry => entry with
                    {
                        SourcePath = RuleFixture.FixtureDigestionSourcePath,
                    }).ToImmutableArray(),
                },
            ]));

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(16),
            fixture.Build());
        var parent = Assert.Single(candidate.RequireDigestionEntries(), entry =>
            !entry.Receipts.ChainAtoms.IsEmpty);

        Assert.Contains(evaluation.Diagnostics, diagnostic => diagnostic.Message.Contains(
            $"entry {parent.AtomId} malformed clause chain",
            StringComparison.Ordinal));
    }

    [Fact]
    public void IngestRejectsUnverifiedNonemptyClauseChain()
    {
        var (sourceBytes, baseline, candidate, parentCapture, childCapture) = MalformedPzgClauseSubset();

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            candidate,
            Snapshot(sourceBytes, [parentCapture, childCapture]),
            baseline));
        var parent = Assert.Single(candidate.RequireDigestionEntries(), entry =>
            !entry.Receipts.ChainAtoms.IsEmpty);

        Assert.Contains(
            $"ingest clause chain parent {parent.AtomId} lacks verified clause-plan proof",
            exception.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            $"entry {parent.AtomId} malformed clause chain",
            exception.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionPreservesInheritedRegisteredAtomNotClaimedByAPlan()
    {
        var bytes = Encoding.UTF8.GetBytes("registered atom");
        var atom = Atom("theorem/clause/fixture", bytes);
        var captured = DigestionCasStore.Capture(bytes);
        var ledger = Ledger(
            [],
            CasEntry("registered-atom", atom, captured.Reference));

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(bytes, [captured]),
            ledger,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(atom));

        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(AtomId(atom)));
        Assert.Empty(result.Findings);
    }

    [Fact]
    public void InheritedGictGenericChainIsNotRecheckedByAdmissionButIngestRejectsMissingPlan()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。first。\n\n**定理 1.2(B)**。second。\n");
        var claims = GictAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules).Claims;
        Assert.Equal(2, claims.Length);
        var parentCapture = DigestionCasStore.Capture(claims[0].RawBytes.AsSpan());
        var childCapture = DigestionCasStore.Capture(claims[1].RawBytes.AsSpan());
        var loaded = Ledger(
            [],
            CasEntry("parent", claims[0], parentCapture.Reference),
            CasEntry("generic-child", claims[1], childCapture.Reference));
        var source = Assert.Single(loaded.RequireDigestionSources());
        var parentId = AtomId(claims[0]);
        var childId = AtomId(claims[1]);
        var parent = Assert.Single(source.Entries, entry => entry.AtomId == parentId);
        var ledger = loaded.WithDigestionSources(
        [
            source with
            {
                GenreRegistryProjection = GenreRegistryProjection.Available(
                    GenreRegistryCheck.Collected([])),
                Entries =
                [
                    parent with
                    {
                        Receipts = parent.Receipts with { ChainAtoms = [childId] },
                    },
                    Assert.Single(source.Entries, entry => entry.AtomId == childId),
                ],
            },
        ]);
        var snapshot = Snapshot(sourceBytes, [parentCapture, childCapture]);

        var alignment = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Admission);
        var exception = Assert.Throws<FormatException>(() =>
            DigestionIngestor.Plan(ledger, snapshot, ledger));

        Assert.Equal(DigestionReceiptAlignment.Seen, alignment.AlignmentFor(parentId));
        Assert.Equal(DigestionReceiptAlignment.Seen, alignment.AlignmentFor(childId));
        Assert.Empty(alignment.Findings);
        Assert.Contains($"ingest clause chain parent {parentId} lacks verified clause-plan proof", exception.Message);
        Assert.Contains("parent CAS blob has no clause plan", exception.Message);
    }

    [Fact]
    public void IngestDoesNotDecomposeAbsorbedClosedClausePlanParent()
    {
        const string claim = """
            **定理 18.7(已闭合链)**。first clause。

            **推论:第二子句**;the full plan has two clauses。

            """;
        var sourceBytes = Encoding.UTF8.GetBytes("# PZG\n\n" + claim);
        var atomized = PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var parent = Assert.Single(atomized.Claims);
        Assert.Single(atomized.ClausePlans);
        var captured = DigestionCasStore.Capture(parent.RawBytes.AsSpan());
        var loaded = WithAtomizer(
            Ledger([], CasEntry("parent", parent, captured.Reference)),
            AtomizerRegistry.PzgId);
        var source = Assert.Single(loaded.RequireDigestionSources());
        var absorbedParent = Assert.Single(source.Entries) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
        };
        var ledger = loaded.WithDigestionSources(
            [source with { Entries = [absorbedParent] }]);

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, [captured]),
            ledger);

        var result = Assert.Single(Assert.Single(plan.Document.RequireDigestionSources()).Entries);
        Assert.Equal(AtomId(parent), result.AtomId);
        Assert.Equal(absorbedParent.Fingerprints, result.Fingerprints);
        Assert.Equal(absorbedParent.ProjectedStatus, result.ProjectedStatus);
        Assert.Equal(absorbedParent.CasRef, result.CasRef);
        Assert.Empty(result.Receipts.ChainAtoms);
        Assert.Equal(0, plan.ResidualOpenAdded);
        Assert.Empty(plan.CasObjects);
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
        var baseline = WithAtomizer(
            Ledger([], CasEntry("parent", parent, parentCapture.Reference)),
            AtomizerRegistry.PzgId);
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var firstId = firstCapture.Reference["sha256:".Length..];
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var target = Encoding.UTF8.GetBytes(DigestionTestSupport.Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var targetStatementId = FrozenStatementReceiptTestData.Id('a');
        DigestionLedgerEntry Complete(
            DigestionLedgerEntry template,
            string atomId,
            DigestionAtom atom,
            ImmutableArray<string> chainAtoms) => template with
        {
            AtomId = atomId,
            Fingerprints = atom.Fingerprints,
            CoverageGids = [gid],
            Receipts = new DigestionReceipts(
                [new DigestionCoverageReceipt(gid, atom.Fingerprints.RawSha256, targetStatementId)],
                [new DigestionScribeReceipt(gid, definitionHash, emissionHash)],
                [],
                chainAtoms,
                null),
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
            CasRef = atom.Fingerprints.RawSha256,
        };
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    Complete(parentEntry, AtomId(parent), parent, [firstId]),
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
        var snapshot = DigestionTestSupport.Snapshot([
            ("docs/source.md", sourceBytes),
            DigestionTestSupport.CasFile(parent),
            DigestionTestSupport.CasFile(first),
            (targetPath, target),
            (record.DefinitionPath, definition),
            (record.EmissionPath, emission),
            .. FrozenStatementReceiptTestData.LedgerFiles(
                new FrozenStatementReceiptTestData.Module(
                    targetPath,
                    targetStatementId,
                    [])),
        ]);

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            candidate,
            snapshot,
            DigestionTestSupport.AcceptedLean(targetPath),
            VerifiedScribeEmissions.Create([record]),
            baselineDocument: baseline);

        var evaluatedParent = Assert.Single(
            evaluation.Entries,
            entry => entry.Entry.AtomId == AtomId(parent));
        Assert.NotEqual(DigestionMigrationState.Absorbed, evaluatedParent.DerivedStatus.Migration);
        Assert.Contains(evaluation.Findings, finding => finding.Contains(
            $"entry {AtomId(parent)} handwritten status",
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
        var baseline = Ledger(
            [],
            CasEntry("parent", parent, parentCapture.Reference));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var firstId = firstCapture.Reference["sha256:".Length..];
        var invalidId = invalidCapture.Reference["sha256:".Length..];
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    parentEntry with
                    {
                        Receipts = parentEntry.Receipts with { ChainAtoms = [firstId, invalidId] },
                    },
                    ChildEntry(parentEntry, firstId, first, firstCapture.Reference),
                    ChildEntry(parentEntry, invalidId, invalidSecond, invalidCapture.Reference),
                ],
            },
        ]);
        var atomized = new AtomizedTheoryDocument(
            [parent],
            [new DigestionSlice(true, parent.RawBytes)],
            [new DigestionClausePlan(parent, [first, plannedSecond])],
            GenreRegistryCheck.NoGenreRegistry);

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

    private static DigestionAtom Atom(string _, byte[] bytes) => new(
        0,
        bytes.Length,
        ImmutableArray.CreateRange(bytes),
        DigestionFingerprint.Compute(bytes),
        []);

    private static DigestionAtom SpannedAtom(
        DigestionAtom parent,
        int start,
        int end,
        int _) => new(
            parent.StartByte + start,
            parent.StartByte + end,
            parent.RawBytes[start..end],
            DigestionFingerprint.Compute(parent.RawBytes.AsSpan()[start..end]),
            parent.Context);

    private static AtomizedTheoryDocument Atomized(DigestionAtom atom) => new(
        [atom],
        [new DigestionSlice(true, atom.RawBytes)],
        GenreRegistryCheck.NoGenreRegistry);

    private static (
        byte[] SourceBytes,
        BackfillInventoryDocument Baseline,
        BackfillInventoryDocument Candidate,
        DigestionCasObject ParentCapture,
        DigestionCasObject ChildCapture) MalformedPzgClauseSubset()
    {
        const string claim = """
            **定理 18.7(链验证)**。first clause。

            **推论:第二子句**;the full plan has two clauses。

            """;
        var sourceBytes = Encoding.UTF8.GetBytes("# PZG\n\n" + claim);
        var atomized = PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var parent = Assert.Single(atomized.Claims);
        var first = Assert.Single(atomized.ClausePlans).Children[0];
        var parentCapture = DigestionCasStore.Capture(parent.RawBytes.AsSpan());
        var childCapture = DigestionCasStore.Capture(first.RawBytes.AsSpan());
        var baseline = WithAtomizer(
            Ledger([], CasEntry("parent", parent, parentCapture.Reference)),
            AtomizerRegistry.PzgId);
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var childId = childCapture.Reference["sha256:".Length..];
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    parentEntry with
                    {
                        Receipts = parentEntry.Receipts with { ChainAtoms = [childId] },
                    },
                    ChildEntry(parentEntry, childId, first, childCapture.Reference),
                ],
            },
        ]);
        return (sourceBytes, baseline, candidate, parentCapture, childCapture);
    }

    private static DigestionLedgerEntry ChildEntry(
        DigestionLedgerEntry parent,
        string atomId,
        DigestionAtom child,
        string casRef) => parent with
        {
            AtomId = atomId,
            Fingerprints = child.Fingerprints,
            CoverageGids = [],
            Receipts = new DigestionReceipts([], [], [], [], null),
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Residual,
                DigestionTruthState.Open),
            CasRef = casRef,
        };

}
