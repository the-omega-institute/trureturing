using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed record DigestionFrontierFixture(
    BackfillInventoryDocument Document,
    DigestionLedgerEvaluation Evaluation,
    IReadOnlyDictionary<string, string> ContentKinds,
    RepositorySnapshot Snapshot,
    DigestionFrontierProjection Projection)
{
    internal const string QuarantinedId = "quarantined-chain-child";
    internal const string CoverWithheldId = "withheld-definition";
    internal const string StaleId = "acknowledged-stale";
    internal const string ChainChildId = "theorem-chain-child";
    internal const string ChainParentId = "theorem-chain-parent";
    internal const string StructuralChainChildId = "structural-chain-child";
    internal const string StructuralId = "standalone-structural-definition";
    internal const string ClaimId = "formalizable-claim";

    internal static DigestionFrontierFixture Create(
        bool retryDispositions = false,
        string coverKind = "definition",
        DigestionAtomStatusMarker? claimStatusMarker = null)
    {
        var quarantined = Entry(
            "source-a",
            QuarantinedId,
            "theorem",
            quarantine: new DigestionQuarantine(
                "blocked",
                "supply witness",
                "missing-prerequisite"));
        var coverWithheld = Entry(
            "source-a",
            CoverWithheldId,
            coverKind,
            coverDisposition: new DigestionCoverDisposition(
                new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Closed),
                ["D5/S0/Carrier/Probe.probe"],
                [new DigestionDispositionGap("unresolved-subitem", "remaining")]));
        var stale = Entry("source-a", StaleId, "theorem");
        var chainChild = Entry("source-b", ChainChildId, "theorem");
        var chainParent = Entry(
            "source-b",
            ChainParentId,
            "theorem",
            chainAtoms: [QuarantinedId, ChainChildId, StructuralChainChildId],
            gaps:
            [
                new DigestionGap(
                    "chain-migration-incomplete",
                    ChainChildId,
                    DigestionGapSeverity.NonFatal),
            ]);
        var structuralChainChild = Entry("source-b", StructuralChainChildId, "definition");
        var structural = Entry("source-b", StructuralId, "definition");
        var claim = Entry("source-b", ClaimId, "lemma", statusMarker: claimStatusMarker);
        var entries = new[]
        {
            quarantined, coverWithheld, stale, chainChild, chainParent, structuralChainChild,
            structural, claim,
        };
        var sources = entries
            .GroupBy(static item => item.Evaluation.Entry.SourceId, StringComparer.Ordinal)
            .Select(group => new DigestionLedgerSource(
                group.Key,
                "synthetic/" + group.Key + ".md",
                AtomizerRegistry.GenericId,
                group.Key == "source-a" ? [StaleId] : [],
                GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
                group.Select(static item => item.Evaluation.Entry).ToImmutableArray()))
            .ToImmutableArray();
        var document = BackfillInventoryDocument.Create(sources, []);
        var evaluation = new DigestionLedgerEvaluation(
            entries.Select(static item => item.Evaluation).ToImmutableArray(),
            []);
        var contentKinds = entries.ToDictionary(
            static item => item.Evaluation.Entry.AtomId,
            static item => item.Kind,
            StringComparer.Ordinal);
        var rawSnapshot = RawRepositorySnapshot.Create(entries
            .Select(static item => new RawRepositoryEntry(
                DigestionCasStore.RootPath + item.Evaluation.Entry.CasRef["sha256:".Length..],
                item.Evaluation.Atom!.RawBytes)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(rawSnapshot)).Snapshot;
        var projection = DigestionFrontierProjection.Create(
            document,
            evaluation,
            contentKinds,
            retryDispositions);
        return new DigestionFrontierFixture(
            document,
            evaluation,
            contentKinds,
            snapshot,
            projection);
    }

    private static (DigestionEntryEvaluation Evaluation, string Kind) Entry(
        string sourceId,
        string atomId,
        string kind,
        ImmutableArray<string> chainAtoms = default,
        ImmutableArray<DigestionGap> gaps = default,
        DigestionQuarantine? quarantine = null,
        DigestionCoverDisposition? coverDisposition = null,
        DigestionAtomStatusMarker? statusMarker = null)
    {
        var rawBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(kind + ":" + atomId + "\n"));
        var fingerprints = DigestionFingerprint.Compute(rawBytes.AsSpan());
        var status = new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open);
        var entry = new DigestionLedgerEntry(
            sourceId,
            "synthetic/" + sourceId + ".md",
            AtomizerRegistry.GenericId,
            atomId,
            fingerprints,
            [],
            new DigestionReceipts(
                [],
                [],
                chainAtoms.IsDefault ? [] : chainAtoms,
                null,
                quarantine,
                coverDisposition),
            status,
            fingerprints.RawSha256);
        var atom = new DigestionAtom(
            0,
            rawBytes.Length,
            rawBytes,
            fingerprints,
            [],
            statusMarker ?? DigestionAtomStatusMarker.Absent);
        return (
            new DigestionEntryEvaluation(
                entry,
                DigestionReceiptAlignment.Seen,
                atom,
                status,
                false,
                gaps.IsDefault ? [] : gaps),
            kind);
    }
}
