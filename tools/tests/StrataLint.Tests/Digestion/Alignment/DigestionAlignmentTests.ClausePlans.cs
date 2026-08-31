using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void PzgIngestDecomposesAParentAndWritesChildrenAndChainInOnePlan()
    {
        const string claim = """
            **定理 18.7(时间之矢)**〔closed〕。u_t ≠ 0 ⇒ **L(a_{t+1}) > L(a_t)**:长度沿正生成严格单调。

            *证明*。L(a_{t+1}) − L(a_t) = L(u_t) = Σ u_{t,p} log p > 0。∎

            **推论:时间方向来自素数账本增长**;只要未引入逆账本,素数生成动力学单向。逆向运动(负指数)属群化扩张,须显式逆账本并入账(账 O-8)。

            """;
        var sourceBytes = Encoding.UTF8.GetBytes("# PZG\n\n" + claim);
        var parent = Assert.Single(PzgAtomizer.Atomize(
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var parentCapture = DigestionCasStore.Capture(parent.RawBytes.AsSpan());
        var loaded = WithAtomizer(
            Ledger([], CasEntry("parent", parent, parentCapture.Reference)),
            AtomizerRegistry.PzgId);
        var source = Assert.Single(loaded.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var ledger = loaded.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    parentEntry with
                    {
                        Receipts = parentEntry.Receipts with
                        {
                            UnresolvedSubitems = ["secondary-verdict"],
                        },
                    },
                ],
            },
        ]);

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, [parentCapture]),
            ledger);
        var entries = Assert.Single(first.Document.RequireDigestionSources()).Entries;
        var parentId = AtomId(parent);
        var plannedParent = Assert.Single(entries, entry => entry.AtomId == parentId);
        var children = entries.Where(entry => entry.AtomId != parentId).ToArray();

        Assert.Equal(2, first.ResidualOpenAdded);
        Assert.Equal(2, children.Length);
        Assert.Equal(parentCapture.Reference, plannedParent.CasRef);
        Assert.Empty(plannedParent.Receipts.UnresolvedSubitems);
        Assert.Equal(
            children.Select(static child => child.AtomId).Order(StringComparer.Ordinal),
            plannedParent.Receipts.ChainAtoms.Order(StringComparer.Ordinal));
        Assert.All(children, child =>
        {
            Assert.Equal(child.Fingerprints.RawSha256["sha256:".Length..], child.AtomId);
            Assert.Equal(DigestionMigrationState.Residual, child.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, child.ProjectedStatus.Truth);
        });

        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        var migrated = first.Document;
        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, first.CasObjects.Prepend(parentCapture)),
            ledger);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes, secondBytes);
    }

    [Fact]
    public void PzgIngestReusesIdenticalClauseContentAcrossParents()
    {
        const string sharedClause = "**推论:共享子句**;相同字节必须按父 atom 寻址。";
        var sourceBytes = Encoding.UTF8.GetBytes($$"""
            # PZG

            **定理 18.7(甲)**。first parent。

            {{sharedClause}}

            **定理 18.8(乙)**。second parent。

            {{sharedClause}}

            # END

            """);
        var atomized = PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        Assert.Equal(2, atomized.Claims.Length);
        Assert.Equal(2, atomized.ClausePlans.Length);
        var sharedChildren = atomized.ClausePlans
            .Select(static plan => plan.Children[1])
            .ToArray();
        Assert.True(
            sharedChildren[0].RawBytes.AsSpan().SequenceEqual(sharedChildren[1].RawBytes.AsSpan()),
            $"first=[{Encoding.UTF8.GetString(sharedChildren[0].RawBytes.AsSpan())}] "
            + $"second=[{Encoding.UTF8.GetString(sharedChildren[1].RawBytes.AsSpan())}]");
        var parentCaptures = atomized.Claims
            .Select(parent => DigestionCasStore.Capture(parent.RawBytes.AsSpan()))
            .ToArray();
        var ledger = WithAtomizer(
            Ledger(
                [],
                CasEntry("parent-18-7", atomized.Claims[0], parentCaptures[0].Reference),
                CasEntry("parent-18-8", atomized.Claims[1], parentCaptures[1].Reference)),
            AtomizerRegistry.PzgId);

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, parentCaptures),
            ledger);

        var entries = Assert.Single(plan.Document.RequireDigestionSources()).Entries;
        var sharedFingerprint = Assert.Single(sharedChildren
            .Select(static child => child.Fingerprints.RawSha256)
            .Distinct(StringComparer.Ordinal));
        var admittedSharedChildren = entries
            .Where(entry => entry.Fingerprints.RawSha256 == sharedFingerprint)
            .ToArray();
        var admittedSharedChild = Assert.Single(admittedSharedChildren);
        Assert.Equal(sharedFingerprint["sha256:".Length..], admittedSharedChild.AtomId);
        Assert.Equal(3, plan.ResidualOpenAdded);
    }

    [Fact]
    public void PzgIngestRejectsClausePlanWhenOnlyNormalizedParentMatchesFrozenCas()
    {
        const string claim = """
            **定理 18.7(换行视图)**。first clause。

            **推论:第二子句**;line ending normalization must preserve the parent identity。

            """;
        var lfBytes = Encoding.UTF8.GetBytes("# PZG\n\n" + claim);
        var crlfBytes = Encoding.UTF8.GetBytes(
            ("# PZG\n\n" + claim).Replace("\n", "\r\n", StringComparison.Ordinal));
        var lfParent = Assert.Single(PzgAtomizer.Atomize(
            lfBytes,
            DigestionTestSupport.Rules).Claims);
        var crlfParent = Assert.Single(PzgAtomizer.Atomize(
            crlfBytes,
            DigestionTestSupport.Rules).Claims);
        Assert.NotEqual(lfParent.Fingerprints.RawSha256, crlfParent.Fingerprints.RawSha256);
        Assert.Equal(lfParent.Fingerprints.NormalizedSha256, crlfParent.Fingerprints.NormalizedSha256);
        var parentCapture = DigestionCasStore.Capture(lfParent.RawBytes.AsSpan());
        var ledger = WithAtomizer(
            Ledger([], CasEntry("parent", lfParent, parentCapture.Reference)),
            AtomizerRegistry.PzgId);

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            ledger,
            Snapshot(crlfBytes, [parentCapture]),
            ledger));

        Assert.Contains("parent CAS bytes", exception.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("outside")]
    [InlineData("non-unique")]
    [InlineData("overlap")]
    public void AdmissionRejectsUnverifiedNestedChildSpans(string defect)
    {
        var parentBytes = Encoding.UTF8.GetBytes(defect == "non-unique" ? "abcabc" : "abcdef");
        var parent = Atom("theorem/1.1", parentBytes);
        DigestionAtom[] children = defect switch
        {
            "outside" =>
            [
                SpannedAtom(parent, 0, 3, 1),
                new DigestionAtom(
                    3,
                    7,
                    ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("defx")),
                    DigestionFingerprint.Compute(Encoding.UTF8.GetBytes("defx")),
                    parent.Context),
            ],
            "non-unique" => [SpannedAtom(parent, 0, 3, 1), SpannedAtom(parent, 3, 6, 2)],
            "overlap" => [SpannedAtom(parent, 0, 4, 1), SpannedAtom(parent, 2, 6, 2)],
            _ => throw new ArgumentOutOfRangeException(nameof(defect)),
        };
        var parentCapture = DigestionCasStore.Capture(parentBytes);
        var baseline = Ledger(
            [],
            CasEntry("parent", parent, parentCapture.Reference));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var childCaptures = children
            .Select(static child => DigestionCasStore.Capture(child.RawBytes.AsSpan()))
            .ToArray();
        var childIds = childCaptures
            .Select(static capture => capture.Reference["sha256:".Length..])
            .ToImmutableArray();
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    parentEntry with
                    {
                        Receipts = parentEntry.Receipts with { ChainAtoms = childIds },
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
            Snapshot(
                parentBytes,
                childCaptures
                    .Prepend(parentCapture)
                    .DistinctBy(static capture => capture.RelativePath, StringComparer.Ordinal)),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => new AtomizedTheoryDocument(
                [parent],
                [new DigestionSlice(true, parent.RawBytes)],
                [new DigestionClausePlan(parent, children.ToImmutableArray())],
                GenreRegistryCheck.NoGenreRegistry));

        Assert.All(childIds, childId => Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(childId)));
        Assert.Contains(result.Findings, finding => finding.Contains(
            defect == "non-unique" ? "not a unique parent sub-span" : "clause plan",
            StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsAsymmetricRepeatedFirstClauseByUniquenessAlone()
    {
        var parentBytes = Encoding.UTF8.GetBytes("abcabcX");
        var parent = Atom("theorem/1.1", parentBytes);
        DigestionAtom[] children =
        [
            SpannedAtom(parent, 0, 3, 1),
            SpannedAtom(parent, 3, 7, 2),
        ];
        var parentCapture = DigestionCasStore.Capture(parentBytes);
        var childCaptures = children
            .Select(static child => DigestionCasStore.Capture(child.RawBytes.AsSpan()))
            .ToArray();
        var baseline = Ledger(
            [],
            CasEntry("parent", parent, parentCapture.Reference));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var childIds = childCaptures
            .Select(static capture => capture.Reference["sha256:".Length..])
            .ToImmutableArray();
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    parentEntry with
                    {
                        Receipts = parentEntry.Receipts with { ChainAtoms = childIds },
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
            _ => (_, _) => new AtomizedTheoryDocument(
                [parent],
                [new DigestionSlice(true, parent.RawBytes)],
                [new DigestionClausePlan(parent, children.ToImmutableArray())],
                GenreRegistryCheck.NoGenreRegistry));

        Assert.All(childIds, childId => Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(childId)));
        Assert.Contains(result.Findings, finding => finding.Contains(
            "not a unique parent sub-span",
            StringComparison.Ordinal));
    }

    [Fact]
    public void IngestRejectsOverlappingClausePlanBoundaries()
    {
        var parentBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("abcdef"));
        var parent = new DigestionAtom(
            0,
            parentBytes.Length,
            parentBytes,
            DigestionFingerprint.Compute(parentBytes.AsSpan()),
            []);
        var firstBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("abcd"));
        var secondBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("cdef"));
        var first = new DigestionAtom(
            0,
            4,
            firstBytes,
            DigestionFingerprint.Compute(firstBytes.AsSpan()),
            []);
        var second = new DigestionAtom(
            2,
            6,
            secondBytes,
            DigestionFingerprint.Compute(secondBytes.AsSpan()),
            []);
        var invalid = new AtomizedTheoryDocument(
            [parent],
            [new DigestionSlice(true, parentBytes)],
            [new DigestionClausePlan(parent, [first, second])],
            GenreRegistryCheck.NoGenreRegistry);
        var captured = DigestionCasStore.Capture(parentBytes.AsSpan());
        var ledger = Ledger(
            [],
            CasEntry("parent", parent, captured.Reference));

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
            [new DigestionClausePlan(parent, [first, second])],
            GenreRegistryCheck.NoGenreRegistry);
        var captured = DigestionCasStore.Capture(parentBytes.AsSpan());
        var ledger = Ledger(
            [],
            CasEntry("parent", parent, captured.Reference));

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

    [Fact]
    public void AdmissionDoesNotRecheckInheritedClauseChainForUnrelatedDelta()
    {
        var (sourceBytes, _, malformedCandidate, parentCapture, childCapture) =
            MalformedPzgClauseSubset();
        var baseline = malformedCandidate;
        var candidate = malformedCandidate;
        var calls = 0;
        var changes = RawChangeSet.Create(["D5/S3/Probe/Unrelated.lean"]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, [parentCapture, childCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) =>
            {
                calls++;
                return PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
            },
            baselineSnapshot: Snapshot(sourceBytes, [parentCapture, childCapture]),
            changes: changes);

        Assert.Empty(result.Findings);
        Assert.Equal(0, calls);
        var parent = Assert.Single(malformedCandidate.RequireDigestionEntries(), entry =>
            entry.Receipts.ChainAtoms.Length > 0);
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(parent.AtomId));
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(childCapture.Reference["sha256:".Length..]));
        Assert.Empty(result.VerifiedClausePlanParents);
        Assert.Equal(
            0,
            DigestionCasStore.Evaluate(
                candidate,
                Snapshot(sourceBytes, [parentCapture, childCapture]),
                changes).RehashedObjectCount);
    }

    [Fact]
    public void AdmissionRechecksClauseChainWhenReceiptIsInDelta()
    {
        var (sourceBytes, _, malformedCandidate, parentCapture, childCapture) =
            MalformedPzgClauseSubset();
        var baseline = malformedCandidate;
        var candidate = malformedCandidate;
        var calls = 0;
        var parent = Assert.Single(malformedCandidate.RequireDigestionEntries(), entry =>
            entry.Receipts.ChainAtoms.Length > 0);
        var parentPath = $"Meta/Digestion/backfill/source/residual-open/{parent.AtomId}.yaml";

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, [parentCapture, childCapture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) =>
            {
                calls++;
                return PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
            },
            baselineSnapshot: Snapshot(sourceBytes, [parentCapture, childCapture]),
            changes: RawChangeSet.Create([parentPath]));

        Assert.True(calls > 0);
        Assert.Contains(result.Findings, finding => finding.Contains(
            "chain cardinality",
            StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("docs/source.md")]
    [InlineData("Meta/Digestion/atomizers.toml")]
    [InlineData("tools/StrataLint.Engine/Digestion/Atomizers/PzgAtomizer.cs")]
    public void AdmissionRechecksAllClauseChainsWhenAtomizerInputIsInDelta(string changedPath)
    {
        var (sourceBytes, _, candidate, parentCapture, childCapture) =
            MalformedPzgClauseSubset();
        var calls = 0;
        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, [parentCapture, childCapture]),
            candidate,
            DigestionAlignmentMode.Admission,
            _ => (_, _) =>
            {
                calls++;
                return PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
            },
            baselineSnapshot: Snapshot(sourceBytes, [parentCapture, childCapture]),
            changes: RawChangeSet.Create([changedPath]));

        Assert.True(calls > 0);
        Assert.Contains(result.Findings, finding => finding.Contains(
            "chain cardinality",
            StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRechecksClauseChainWhenParentCasIsInDelta()
    {
        var (sourceBytes, _, candidate, parentCapture, childCapture) =
            MalformedPzgClauseSubset();
        var calls = 0;
        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, [parentCapture, childCapture]),
            candidate,
            DigestionAlignmentMode.Admission,
            _ => (_, _) =>
            {
                calls++;
                return PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
            },
            baselineSnapshot: Snapshot(sourceBytes, [parentCapture, childCapture]),
            changes: RawChangeSet.Create([parentCapture.RelativePath]));

        Assert.True(calls > 0);
        Assert.Contains(result.Findings, finding => finding.Contains(
            "chain cardinality",
            StringComparison.Ordinal));
    }

}
