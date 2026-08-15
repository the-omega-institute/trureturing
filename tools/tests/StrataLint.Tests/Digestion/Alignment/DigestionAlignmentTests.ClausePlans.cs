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
        var loaded = BackfillInventoryLoader.Load(
            Ledger([], CasEntry("parent", parent, parentCapture.Reference))
                .Replace(AtomizerRegistry.GictId, AtomizerRegistry.PzgId, StringComparison.Ordinal));
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
                        ReceiptSyntax = null,
                    },
                ],
            },
        ]);

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, [parentCapture]),
            ledger);
        var entries = Assert.Single(first.Document.RequireDigestionSources()).Entries;
        var plannedParent = Assert.Single(entries, static entry => entry.AtomId == "parent");
        var children = entries.Where(static entry => entry.AtomId != "parent").ToArray();

        Assert.Equal(2, first.ResidualOpenAdded);
        Assert.Equal(2, children.Length);
        Assert.Equal(parentCapture.Reference, plannedParent.CasRef);
        Assert.Empty(plannedParent.Receipts.UnresolvedSubitems);
        Assert.Equal(children.Select(static child => child.AtomId), plannedParent.Receipts.ChainAtoms);
        Assert.All(children, child =>
        {
            Assert.StartsWith("theorem/18.7/clause/", child.AstPath, StringComparison.Ordinal);
            Assert.StartsWith(
                "pzg-residual-" + child.Fingerprints.RawSha256["sha256:".Length..] + "-",
                child.AtomId,
                StringComparison.Ordinal);
            Assert.Equal(DigestionMigrationState.Residual, child.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, child.ProjectedStatus.Truth);
        });

        var firstBytes = BackfillInventoryWriter.WriteForIngest(first.Document);
        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));
        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, first.CasObjects.Prepend(parentCapture)),
            ledger);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }

    [Fact]
    public void PzgIngestQualifiesIdenticalClauseBytesByParent()
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
        var ledger = BackfillInventoryLoader.Load(
            Ledger(
                [],
                CasEntry("parent-18-7", atomized.Claims[0], parentCaptures[0].Reference),
                CasEntry("parent-18-8", atomized.Claims[1], parentCaptures[1].Reference))
                .Replace(AtomizerRegistry.GictId, AtomizerRegistry.PzgId, StringComparison.Ordinal));

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
        Assert.Equal(2, admittedSharedChildren.Length);
        Assert.Equal(2, admittedSharedChildren.Select(static child => child.AtomId).Distinct().Count());
        Assert.Equal(4, plan.ResidualOpenAdded);
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
        var ledger = BackfillInventoryLoader.Load(
            Ledger([], CasEntry("parent", lfParent, parentCapture.Reference))
                .Replace(AtomizerRegistry.GictId, AtomizerRegistry.PzgId, StringComparison.Ordinal));

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
                    $"{parent.AstPath}/clause/2",
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
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("parent", parent, parentCapture.Reference)));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var childCaptures = children
            .Select(static child => DigestionCasStore.Capture(child.RawBytes.AsSpan()))
            .ToArray();
        var childIds = childCaptures.Select((capture, index) =>
            "gict-residual-" + capture.Reference["sha256:".Length..] + $"-{index + 1}").ToImmutableArray();
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
                [new DigestionClausePlan(parent.AstPath, children.ToImmutableArray())],
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
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("parent", parent, parentCapture.Reference)));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries);
        var childIds = childCaptures.Select((capture, index) =>
            "gict-residual-" + capture.Reference["sha256:".Length..] + $"-{index + 1}").ToImmutableArray();
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
            _ => (_, _) => new AtomizedTheoryDocument(
                [parent],
                [new DigestionSlice(true, parent.RawBytes)],
                [new DigestionClausePlan(parent.AstPath, children.ToImmutableArray())],
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
            [new DigestionClausePlan(parent.AstPath, [first, second])],
            GenreRegistryCheck.NoGenreRegistry);
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
            [new DigestionClausePlan(parent.AstPath, [first, second])],
            GenreRegistryCheck.NoGenreRegistry);
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

}
