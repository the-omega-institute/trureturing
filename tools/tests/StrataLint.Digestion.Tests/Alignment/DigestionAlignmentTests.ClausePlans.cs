using static StrataLint.TestSupport.DigestionAlignmentFixture;
using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Digestion.Tests;

public sealed partial class DigestionAlignmentTests
{
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
            DigestionAlignmentMode.Admission,
            _ => (_, _) => new AtomizedTheoryDocument(
                [parent],
                [new DigestionSlice(true, parent.RawBytes)],
                [new DigestionClausePlan(parent, children.ToImmutableArray())],
                GenreRegistryCheck.NoGenreRegistry));

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
            DigestionAlignmentMode.Admission,
            _ => (_, _) => new AtomizedTheoryDocument(
                [parent],
                [new DigestionSlice(true, parent.RawBytes)],
                [new DigestionClausePlan(parent, children.ToImmutableArray())],
                GenreRegistryCheck.NoGenreRegistry));

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
            DigestionAlignmentMode.Admission,
            _ => (_, _) =>
            {
                calls++;
                return PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
            },
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
            DigestionAlignmentMode.Admission,
            _ => (_, _) =>
            {
                calls++;
                return PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
            },
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
            DigestionAlignmentMode.Admission,
            _ => (_, _) =>
            {
                calls++;
                return PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
            },
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
            DigestionAlignmentMode.Admission,
            _ => (_, _) =>
            {
                calls++;
                return PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
            },
            changes: RawChangeSet.Create([parentCapture.RelativePath]));

        Assert.True(calls > 0);
        Assert.Contains(result.Findings, finding => finding.Contains(
            "chain cardinality",
            StringComparison.Ordinal));
    }

}
