using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void SelfContainedClauseChain_VerifiesHistoricalParentAfterSameLocatorSourceRewrite()
    {
        var fixture = SelfContainedClauseChain(sameCurrentLocator: true);

        var result = EvaluateSelfContainedClauseChain(fixture);

        Assert.DoesNotContain(result.Findings, finding => finding.Contains(
            "malformed clause chain",
            StringComparison.Ordinal));
        Assert.Contains(fixture.Parent.AtomId, result.ClausePlanChainParents);
        Assert.Contains(fixture.Parent.AtomId, result.VerifiedClausePlanParents);
        Assert.All(fixture.Children, child => Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(child.AtomId)));
    }

    [Fact]
    public void SelfContainedClauseChain_RejectsCardinalityMismatch()
    {
        var fixture = SelfContainedClauseChain();
        var parent = fixture.Parent with
        {
            Receipts = fixture.Parent.Receipts with
            {
                ChainAtoms = [fixture.Children[0].AtomId],
            },
        };
        var ledger = ChainLedger(fixture, parent, fixture.Children);

        var result = EvaluateSelfContainedClauseChain(fixture, ledger);

        AssertMalformedClauseChain(result, fixture.Parent.AtomId, "chain cardinality");
    }

    [Fact]
    public void SelfContainedClauseChain_RejectsDuplicateChild()
    {
        var fixture = SelfContainedClauseChain();
        var parent = fixture.Parent with
        {
            Receipts = fixture.Parent.Receipts with
            {
                ChainAtoms = [fixture.Children[0].AtomId, fixture.Children[0].AtomId],
            },
        };
        var ledger = ChainLedger(fixture, parent, fixture.Children);

        var result = EvaluateSelfContainedClauseChain(fixture, ledger);

        AssertMalformedClauseChain(result, fixture.Parent.AtomId, "duplicate child atom_ids");
    }

    [Fact]
    public void SelfContainedClauseChain_RejectsMissingChildCasBlob()
    {
        var fixture = SelfContainedClauseChain();
        var availableCas = fixture.ChildCaptures
            .Skip(1)
            .Prepend(fixture.ParentCapture);

        var result = EvaluateSelfContainedClauseChain(fixture, casObjects: availableCas);

        Assert.Contains(result.Findings, finding => finding.Contains(
            $"entry {fixture.Children[0].AtomId} CAS blob is missing",
            StringComparison.Ordinal));
        AssertMalformedClauseChain(
            result,
            fixture.Parent.AtomId,
            $"listed child {fixture.Children[0].AtomId} has invalid CAS proof");
    }

    [Fact]
    public void SelfContainedClauseChain_RejectsChildFingerprintMismatch()
    {
        var fixture = SelfContainedClauseChain();
        var child = fixture.Children[0] with
        {
            Fingerprints = new DigestionFingerprints(
                fixture.Children[0].Fingerprints.RawSha256,
                "sha256:" + new string('0', 64)),
        };
        var children = fixture.Children.SetItem(0, child);
        var ledger = ChainLedger(fixture, fixture.Parent, children);

        var result = EvaluateSelfContainedClauseChain(fixture, ledger);

        AssertMalformedClauseChain(result, fixture.Parent.AtomId, "CAS bytes disagree with its fingerprints");
    }

    [Fact]
    public void SelfContainedClauseChain_RejectsChildWhoseBytesAreNotTheParentSlice()
    {
        var fixture = SelfContainedClauseChain();
        var invalidBytes = Encoding.UTF8.GetBytes("rewritten first child\n");
        var invalidCapture = DigestionCasStore.Capture(invalidBytes);
        const string invalidId = "pzg-residual-rewritten-child";
        var invalidChild = fixture.Children[0] with
        {
            AtomId = invalidId,
            Fingerprints = DigestionFingerprint.Compute(invalidBytes),
            CasRef = invalidCapture.Reference,
        };
        var children = fixture.Children.SetItem(0, invalidChild);
        var parent = fixture.Parent with
        {
            Receipts = fixture.Parent.Receipts with
            {
                ChainAtoms = [invalidId, fixture.Children[1].AtomId],
            },
        };
        var ledger = ChainLedger(fixture, parent, children);
        var casObjects = fixture.ChildCaptures
            .Skip(1)
            .Prepend(invalidCapture)
            .Prepend(fixture.ParentCapture);

        var result = EvaluateSelfContainedClauseChain(fixture, ledger, casObjects);

        AssertMalformedClauseChain(result, fixture.Parent.AtomId, "bytes differ from parent CAS plan member");
    }

    [Fact]
    public void SelfContainedClauseChain_RejectsChildOrderMismatch()
    {
        var fixture = SelfContainedClauseChain();
        var parent = fixture.Parent with
        {
            Receipts = fixture.Parent.Receipts with
            {
                ChainAtoms = [fixture.Children[1].AtomId, fixture.Children[0].AtomId],
            },
        };
        var ledger = ChainLedger(fixture, parent, fixture.Children);

        var result = EvaluateSelfContainedClauseChain(fixture, ledger);

        AssertMalformedClauseChain(result, fixture.Parent.AtomId, "chain order differs from parent CAS plan");
    }

    [Fact]
    public void SelfContainedClauseChain_RejectsMissingParentCasBlob()
    {
        var fixture = SelfContainedClauseChain();

        var result = EvaluateSelfContainedClauseChain(fixture, casObjects: fixture.ChildCaptures);

        Assert.Contains(result.Findings, finding => finding.Contains(
            $"entry {fixture.Parent.AtomId} CAS blob is missing",
            StringComparison.Ordinal));
        AssertMalformedClauseChain(result, fixture.Parent.AtomId, "parent CAS proof is invalid");
    }

    [Fact]
    public void SelfContainedClauseChain_RejectsParentCasHashMismatch()
    {
        var fixture = SelfContainedClauseChain();
        var corrupted = new RawRepositoryEntry(
            fixture.ParentCapture.RelativePath,
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("corrupted parent CAS bytes")));

        var result = EvaluateSelfContainedClauseChain(
            fixture,
            casObjects: fixture.ChildCaptures,
            extraEntries: [corrupted]);

        Assert.Contains(result.Findings, finding => finding.Contains(
            $"entry {fixture.Parent.AtomId} CAS blob hash mismatch",
            StringComparison.Ordinal));
        AssertMalformedClauseChain(result, fixture.Parent.AtomId, "parent CAS proof is invalid");
    }

    [Fact]
    public void SelfContainedClauseChain_RejectsRecordedChainWhenParentCasHasNoClausePlan()
    {
        var currentSourceBytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 99.9(Current)**. current source claim.\n");
        var parentBytes = Encoding.UTF8.GetBytes("**定理 1.1(Single)**. one indivisible claim.\n");
        var childBytes = Encoding.UTF8.GetBytes("one indivisible claim.\n");
        var parent = Atom("theorem/1.1", parentBytes);
        var child = Atom("theorem/1.1/clause/1", childBytes);
        var parentCapture = DigestionCasStore.Capture(parentBytes);
        var childCapture = DigestionCasStore.Capture(childBytes);
        var baseline = WithAtomizer(
            Ledger([], CasEntry("parent", parent, parentCapture.Reference)),
            AtomizerRegistry.PzgId);
        var source = Assert.Single(baseline.RequireDigestionSources());
        var parentEntry = Assert.Single(source.Entries) with
        {
            Receipts = Assert.Single(source.Entries).Receipts with { ChainAtoms = ["child"] },
        };
        var childEntry = ChildEntry(parentEntry, "child", child, childCapture.Reference);
        var ledger = baseline.WithDigestionSources(
        [
            source with { Entries = [parentEntry, childEntry] },
        ]);
        var fixture = new SelfContainedClauseChainFixture(
            currentSourceBytes,
            ledger,
            parentEntry,
            [childEntry],
            parentCapture,
            [childCapture]);

        var result = EvaluateSelfContainedClauseChain(fixture);

        AssertMalformedClauseChain(result, parentEntry.AtomId, "parent CAS blob has no clause plan");
    }

    private static SelfContainedClauseChainFixture SelfContainedClauseChain(
        bool sameCurrentLocator = false)
    {
        const string historicalClaim = """
            **定理 18.7(Historical)**. first historical clause.

            **推论:Historical second clause**. second historical clause.

            """;
        var historicalSourceBytes = Encoding.UTF8.GetBytes("# PZG\n\n" + historicalClaim);
        var atomized = PzgAtomizer.Atomize(historicalSourceBytes, DigestionTestSupport.Rules);
        var parent = Assert.Single(atomized.Claims);
        var children = Assert.Single(atomized.ClausePlans).Children;
        var parentCapture = DigestionCasStore.Capture(parent.RawBytes.AsSpan());
        var childCaptures = children
            .Select(static child => DigestionCasStore.Capture(child.RawBytes.AsSpan()))
            .ToImmutableArray();
        var baseline = WithAtomizer(
            Ledger([], CasEntry("parent", parent, parentCapture.Reference)),
            AtomizerRegistry.PzgId);
        var source = Assert.Single(baseline.RequireDigestionSources());
        var baselineParent = Assert.Single(source.Entries);
        var childIds = childCaptures
            .Select((capture, index) =>
                $"pzg-residual-{capture.Reference["sha256:".Length..]}-{index + 1}")
            .ToImmutableArray();
        var parentEntry = baselineParent with
        {
            Receipts = baselineParent.Receipts with { ChainAtoms = childIds },
        };
        var childEntries = children
            .Select((child, index) => ChildEntry(
                parentEntry,
                childIds[index],
                child,
                childCaptures[index].Reference))
            .ToImmutableArray();
        var ledger = baseline.WithDigestionSources(
        [
            source with { Entries = [parentEntry, .. childEntries] },
        ]);
        var currentClaim = sameCurrentLocator
            ? """
                **定理 18.7(Current)**. rewritten current first clause.

                **推论:Current second clause**. rewritten current second clause.

                """
            : "**定理 99.9(Current)**. unrelated current source claim.\n";
        var currentSourceBytes = Encoding.UTF8.GetBytes("# PZG\n\n" + currentClaim);

        return new SelfContainedClauseChainFixture(
            currentSourceBytes,
            ledger,
            parentEntry,
            childEntries,
            parentCapture,
            childCaptures);
    }

    private static BackfillInventoryDocument ChainLedger(
        SelfContainedClauseChainFixture fixture,
        DigestionLedgerEntry parent,
        IEnumerable<DigestionLedgerEntry> children)
    {
        var source = Assert.Single(fixture.Ledger.RequireDigestionSources());
        return fixture.Ledger.WithDigestionSources(
        [
            source with { Entries = children.Prepend(parent).ToImmutableArray() },
        ]);
    }

    private static DigestionLedgerAlignment EvaluateSelfContainedClauseChain(
        SelfContainedClauseChainFixture fixture,
        BackfillInventoryDocument? ledger = null,
        IEnumerable<DigestionCasObject>? casObjects = null,
        IEnumerable<RawRepositoryEntry>? extraEntries = null)
    {
        ledger ??= fixture.Ledger;
        casObjects ??= fixture.ChildCaptures.Prepend(fixture.ParentCapture);
        return DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(
                fixture.CurrentSourceBytes,
                casObjects,
                extraEntries: extraEntries),
            ledger,
            DigestionAlignmentMode.Ingest);
    }

    private static void AssertMalformedClauseChain(
        DigestionLedgerAlignment result,
        string parentId,
        string reason) =>
        Assert.Contains(result.Findings, finding =>
            finding.StartsWith($"entry {parentId} malformed clause chain:", StringComparison.Ordinal)
            && finding.Contains(reason, StringComparison.Ordinal));

    private sealed record SelfContainedClauseChainFixture(
        byte[] CurrentSourceBytes,
        BackfillInventoryDocument Ledger,
        DigestionLedgerEntry Parent,
        ImmutableArray<DigestionLedgerEntry> Children,
        DigestionCasObject ParentCapture,
        ImmutableArray<DigestionCasObject> ChildCaptures);
}
