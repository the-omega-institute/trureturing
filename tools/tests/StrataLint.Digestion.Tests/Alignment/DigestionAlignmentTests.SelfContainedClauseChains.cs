using static StrataLint.TestSupport.DigestionAlignmentFixture;
using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Digestion.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void SelfContainedClauseChain_VerifiesHistoricalParentAfterSameLocatorSourceRewrite()
    {
        var fixture = SelfContainedClauseChain(sameCurrentNumber: true);

        var result = EvaluateSelfContainedClauseChain(fixture);

        Assert.DoesNotContain(result.Findings, finding => finding.Contains(
            "malformed clause chain",
            StringComparison.Ordinal));
        Assert.Contains(fixture.Parent.AtomId, result.VerifiedClausePlanParents);
        Assert.All(fixture.Children, child => Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(child.AtomId)));
    }

    [Fact]
    public void CrossSourceChainAlignmentIsIndependentOfSourceOrder()
    {
        var fixture = SelfContainedClauseChain();
        var originalSource = Assert.Single(fixture.Ledger.RequireDigestionSources());
        var externalChild = fixture.Children[0] with
        {
            SourceId = "child-owner",
            SourcePath = "docs/child-owner.md",
        };
        var localChild = fixture.Children[1] with
        {
            SourceId = "chain-owner",
            SourcePath = "docs/chain-owner.md",
        };
        var parent = fixture.Parent with
        {
            SourceId = "chain-owner",
            SourcePath = "docs/chain-owner.md",
        };
        var childOwner = originalSource with
        {
            SourceId = "child-owner",
            SourcePath = "docs/child-owner.md",
            Entries = [externalChild],
        };
        var chainOwner = originalSource with
        {
            SourceId = "chain-owner",
            SourcePath = "docs/chain-owner.md",
            Entries = [parent, localChild],
        };
        var childOwnerSourceBytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n" + Encoding.UTF8.GetString(fixture.ParentCapture.Bytes.AsSpan()));
        var snapshot = Snapshot(
            childOwnerSourceBytes,
            fixture.ChildCaptures.Prepend(fixture.ParentCapture),
            sourcePath: childOwner.SourcePath,
            extraEntries:
            [
                new RawRepositoryEntry(
                    chainOwner.SourcePath,
                    ImmutableArray.CreateRange(fixture.CurrentSourceBytes)),
            ]);

        DigestionLedgerAlignment Evaluate(params DigestionLedgerSource[] sources) =>
            DigestionLedgerAligner.Evaluate(
                fixture.Ledger.WithDigestionSources([.. sources]),
                snapshot,
                mode: DigestionAlignmentMode.Ingest);

        var childOwnerFirst = Evaluate(childOwner, chainOwner);
        var chainOwnerFirst = Evaluate(chainOwner, childOwner);

        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            childOwnerFirst.AlignmentFor(externalChild.AtomId));
        Assert.Equal(
            childOwnerFirst.AlignmentFor(externalChild.AtomId),
            chainOwnerFirst.AlignmentFor(externalChild.AtomId));
        Assert.NotNull(childOwnerFirst.AtomFor(externalChild.AtomId));
        Assert.NotNull(chainOwnerFirst.AtomFor(externalChild.AtomId));
    }

    [Fact]
    public void AdmissionRevalidatesInheritedChainAcrossContentDeduplicationSourceMove()
    {
        var fixture = SelfContainedClauseChain();
        var baselineSource = Assert.Single(fixture.Ledger.RequireDigestionSources());
        var movedSource = baselineSource with
        {
            SourceId = "content-owner",
            SourcePath = "docs/content-owner.md",
            Entries = fixture.Children.Skip(1).Select(child => child with
            {
                SourceId = "content-owner",
                SourcePath = "docs/content-owner.md",
            }).ToImmutableArray(),
        };
        var candidate = fixture.Ledger.WithDigestionSources(
        [
            baselineSource with { Entries = [fixture.Parent, fixture.Children[0]] },
            movedSource,
        ]);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(
                fixture.CurrentSourceBytes,
                fixture.ChildCaptures.Prepend(fixture.ParentCapture)),
            DigestionAlignmentMode.Admission,
            changes: RawChangeSet.Create([baselineSource.SourcePath]));

        Assert.DoesNotContain(result.Findings, finding => finding.Contains(
            "malformed clause chain",
            StringComparison.Ordinal));
        Assert.Contains(fixture.Parent.AtomId, result.VerifiedClausePlanParents);
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(fixture.Children[0].AtomId));
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(fixture.Children[1].AtomId));
    }

    [Fact]
    public void IngestAcceptsClauseChainChildOwnedByAnotherSource()
    {
        var fixture = SelfContainedClauseChain();
        var parentSource = Assert.Single(fixture.Ledger.RequireDigestionSources());
        var contentOwner = parentSource with
        {
            SourceId = "content-owner",
            SourcePath = "docs/content-owner.md",
            Entries = fixture.Children.Skip(1).Select(child => child with
            {
                SourceId = "content-owner",
                SourcePath = "docs/content-owner.md",
            }).ToImmutableArray(),
        };
        var ledger = fixture.Ledger.WithDigestionSources(
        [
            parentSource with { Entries = [fixture.Parent, fixture.Children[0]] },
            contentOwner,
        ]);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(
                fixture.CurrentSourceBytes,
                fixture.ChildCaptures.Prepend(fixture.ParentCapture),
                extraEntries:
                [
                    new RawRepositoryEntry(
                        contentOwner.SourcePath,
                        ImmutableArray.CreateRange(fixture.CurrentSourceBytes)),
                ]),
            DigestionAlignmentMode.Ingest);

        Assert.DoesNotContain(result.Findings, finding => finding.Contains(
            "malformed clause chain",
            StringComparison.Ordinal));
        Assert.Contains(fixture.Parent.AtomId, result.VerifiedClausePlanParents);
        Assert.All(fixture.Children, child => Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(child.AtomId)));
    }

    [Fact]
    public void IngestRejectsClauseChainChildAbsentFromGlobalInventory()
    {
        var fixture = SelfContainedClauseChain();
        var missingChild = fixture.Children[1];
        var ledger = ChainLedger(
            fixture,
            fixture.Parent,
            fixture.Children.Take(1));

        var result = EvaluateSelfContainedClauseChain(fixture, ledger);

        AssertMalformedClauseChain(
            result,
            fixture.Parent.AtomId,
            $"listed child {missingChild.AtomId} is absent from the global inventory");
        Assert.DoesNotContain(fixture.Parent.AtomId, result.VerifiedClausePlanParents);
    }

    [Fact]
    public void AdmissionRevalidatesChangedChainEvenWhenParentContentIsSeen()
    {
        var fixture = SelfContainedClauseChain();
        var changedParent = fixture.Parent with
        {
            Receipts = fixture.Parent.Receipts with
            {
                ChainAtoms = [fixture.Children[0].AtomId],
            },
        };
        var candidate = ChainLedger(fixture, changedParent, fixture.Children);
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n" + Encoding.UTF8.GetString(fixture.ParentCapture.Bytes.AsSpan()));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(
                sourceBytes,
                fixture.ChildCaptures.Prepend(fixture.ParentCapture)),
            DigestionAlignmentMode.Admission);

        AssertMalformedClauseChain(result, fixture.Parent.AtomId, "chain cardinality");
        Assert.DoesNotContain(fixture.Parent.AtomId, result.VerifiedClausePlanParents);
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

        AssertMalformedClauseChain(
            result,
            fixture.Parent.AtomId,
            "bytes differ from parent CAS plan member");
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
        var invalidId = invalidCapture.Reference["sha256:".Length..];
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

        AssertMalformedClauseChain(
            result,
            fixture.Parent.AtomId,
            "bytes differ from parent CAS plan member");
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
        var childId = childCapture.Reference["sha256:".Length..];
        var parentEntry = Assert.Single(source.Entries) with
        {
            Receipts = Assert.Single(source.Entries).Receipts with { ChainAtoms = [childId] },
        };
        var childEntry = ChildEntry(parentEntry, childId, child, childCapture.Reference);
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

        AssertMalformedClauseChain(result, parentEntry.AtomId, "clause plan has no proper claim decomposition");
    }

    private static SelfContainedClauseChainFixture SelfContainedClauseChain(
        bool sameCurrentNumber = false)
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
            .Select(static capture => capture.Reference["sha256:".Length..])
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
        var currentClaim = sameCurrentNumber
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
