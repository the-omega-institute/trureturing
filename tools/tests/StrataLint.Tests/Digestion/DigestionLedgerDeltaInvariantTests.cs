using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void UnchangedCompleteWitnessInPartialDirectoryRetainsPartialLatch()
    {
        var evaluation = EvaluateCompleteWitness(
            DigestionMigrationState.Partial,
            RawChangeSet.Create(["notes/unrelated.txt"]),
            includeVerifiedScribeWitness: true);

        Assert.Equal(
            DigestionMigrationState.Partial,
            Assert.Single(evaluation.Entries).DerivedStatus.Migration);
    }

    [Fact]
    public void ChildOnlyAbsorptionReleasesCoveredParentPartialLatch()
    {
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var parentAtom = CompleteWitnessAtom();
        var childAtom = CompleteWitnessAtom("manual child specification receipt\n");
        var parentId = parentAtom.Fingerprints.RawSha256["sha256:".Length..];
        var childId = childAtom.Fingerprints.RawSha256["sha256:".Length..];
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var parentReceipts = CompleteWitnessReceipts(
            parentAtom,
            gid,
            definitionHash,
            emissionHash) with
        {
            ChainAtoms = [childId],
        };
        var childReceipts = CompleteWitnessReceipts(
            childAtom,
            gid,
            definitionHash,
            emissionHash);
        var baseline = DigestionTestSupport.Document(
            AtomizerRegistry.NoAtomizerId,
            [
                DigestionTestSupport.Entry(
                    parentAtom,
                    parentId,
                    AtomizerRegistry.NoAtomizerId,
                    DigestionMigrationState.Partial,
                    DigestionTruthState.Closed,
                    [gid],
                    parentReceipts,
                    sourceId: AtomizerRegistry.GictId),
                DigestionTestSupport.Entry(
                    childAtom,
                    childId,
                    AtomizerRegistry.NoAtomizerId,
                    DigestionMigrationState.Partial,
                    DigestionTruthState.Closed,
                    [gid],
                    childReceipts,
                    sourceId: AtomizerRegistry.GictId),
            ],
            sourceId: AtomizerRegistry.GictId);
        var candidateSource = Assert.Single(baseline.RequireDigestionSources());
        var candidate = baseline.WithDigestionSources(
        [
            candidateSource with
            {
                Entries = candidateSource.Entries.Select(entry =>
                    entry.AtomId == childId
                        ? entry with
                        {
                            ProjectedStatus = new DigestionStatus(
                                DigestionMigrationState.Absorbed,
                                DigestionTruthState.Closed),
                        }
                        : entry).ToImmutableArray(),
            },
        ]);
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var snapshot = Snapshot([
            ("docs/source.md", Encoding.UTF8.GetBytes("manual specification receipu\n")),
            CasFile(parentAtom),
            CasFile(childAtom),
            (targetPath, target),
            (ScribeEmissionAttestation.DefinitionPath(gid), definition),
            (ScribeEmissionAttestation.EmissionPath(gid), emission),
            .. FrozenLedgerFiles(targetPath),
        ]);
        var verifiedEmissions = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                gid,
                ScribeEmissionAttestation.DefinitionPath(gid),
                definitionHash,
                ScribeEmissionAttestation.EmissionPath(gid),
                emissionHash),
        ]);

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            candidate,
            snapshot,
            AcceptedLean(targetPath),
            verifiedEmissions,
            baselineDocument: baseline,
            baselineSnapshot: snapshot,
            changes: StatusMoveChanges(childId));

        Assert.Equal(
            DigestionMigrationState.Absorbed,
            Assert.Single(evaluation.Entries, entry => entry.Entry.AtomId == childId)
                .DerivedStatus.Migration);
        Assert.Equal(
            DigestionMigrationState.Absorbed,
            Assert.Single(evaluation.Entries, entry => entry.Entry.AtomId == parentId)
                .DerivedStatus.Migration);
    }

    [Fact]
    public void ByteIdenticalStatusMoveChangesEntryByStableIdentity()
    {
        var atom = CompleteWitnessAtom();
        var baselineEntry = Assert.Single(Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed,
            atomizer: AtomizerRegistry.NoAtomizerId).RequireDigestionEntries());
        var movedEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
        };
        var oldPath = EntryPath(DigestionMigrationState.Partial);
        var newPath = EntryPath(DigestionMigrationState.Absorbed);

        Assert.Equal(
            BackfillInventoryWriter.WriteAtom(baselineEntry).ToArray(),
            BackfillInventoryWriter.WriteAtom(movedEntry).ToArray());
        Assert.True(DigestionCasStore.EntryChanged(
            movedEntry,
            RawChangeSet.CreateWithKinds([(oldPath, RawChangeKind.Deleted)])));
        Assert.True(DigestionCasStore.EntryChanged(
            movedEntry,
            RawChangeSet.CreateWithKinds([(newPath, RawChangeKind.Added)])));
    }

    [Fact]
    public void UnsupportedStatusMoveIsRejectedByProjectedStatusComparison()
    {
        var evaluation = EvaluateCompleteWitness(
            DigestionMigrationState.Absorbed,
            StatusMoveChanges(),
            includeVerifiedScribeWitness: false);
        var entry = Assert.Single(evaluation.Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, entry.Alignment);
        Assert.Equal(DigestionMigrationState.Partial, entry.DerivedStatus.Migration);
        Assert.Contains(evaluation.Findings, finding => finding.Contains(
            "handwritten status absorbed-closed differs from derived partial-closed",
            StringComparison.Ordinal));
    }

    [Fact]
    public void SupportedStatusMoveIsAdmittedFromCurrentWitness()
    {
        var evaluation = EvaluateCompleteWitness(
            DigestionMigrationState.Absorbed,
            StatusMoveChanges(),
            includeVerifiedScribeWitness: true);
        var entry = Assert.Single(evaluation.Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, entry.Alignment);
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            entry.DerivedStatus);
        Assert.DoesNotContain(evaluation.Findings, finding => finding.Contains(
            "handwritten status",
            StringComparison.Ordinal));
    }

    [Fact]
    public void CoverageVerifierRejectsTouchedTargetWhoseForkPointIdentityIsUnchanged()
    {
        var evaluation = EvaluateCompleteWitness(
            DigestionMigrationState.Partial,
            RawChangeSet.Create(["D5/S0/Carrier/Probe.lean"]),
            includeVerifiedScribeWitness: true,
            coverageStatementId: FrozenStatementReceiptTestData.Id('0'));

        Assert.Contains(
            Assert.Single(evaluation.Entries).Gaps,
            gap => gap.Code == "coverage-receipt-mismatch");
    }

    private static DigestionLedgerEvaluation EvaluateCompleteWitness(
        DigestionMigrationState candidateMigration,
        RawChangeSet changes,
        bool includeVerifiedScribeWitness,
        string? coverageStatementId = null)
    {
        var atom = CompleteWitnessAtom();
        var currentSource = Encoding.UTF8.GetBytes("manual specification receipu\n");
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var baseline = Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed,
            gid,
            new DigestionCoverageReceipt(
                gid,
                atom.Fingerprints.RawSha256,
                coverageStatementId ?? TestModuleStatementId),
            new DigestionScribeReceipt(gid, definitionHash, emissionHash),
            atomizer: AtomizerRegistry.NoAtomizerId);
        var candidate = Ledger(
            atom,
            candidateMigration,
            DigestionTruthState.Closed,
            gid,
            new DigestionCoverageReceipt(
                gid,
                atom.Fingerprints.RawSha256,
                coverageStatementId ?? TestModuleStatementId),
            new DigestionScribeReceipt(gid, definitionHash, emissionHash),
            atomizer: AtomizerRegistry.NoAtomizerId);
        var snapshot = Snapshot([
            ("docs/source.md", currentSource),
            CasFile(atom),
            (targetPath, target),
            (ScribeEmissionAttestation.DefinitionPath(gid), definition),
            (ScribeEmissionAttestation.EmissionPath(gid), emission),
            .. FrozenLedgerFiles(targetPath),
        ]);
        var verifiedEmissions = includeVerifiedScribeWitness
            ? VerifiedScribeEmissions.Create(
            [
                new ScribeEmissionRecord(
                    gid,
                    ScribeEmissionAttestation.DefinitionPath(gid),
                    definitionHash,
                    ScribeEmissionAttestation.EmissionPath(gid),
                    emissionHash),
            ])
            : null;

        return DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            candidate,
            snapshot,
            AcceptedLean(targetPath),
            verifiedEmissions,
            baselineDocument: baseline,
            baselineSnapshot: snapshot,
            changes: changes);
    }

    private static DigestionAtom CompleteWitnessAtom(
        string receiptText = "manual specification receipt\n")
    {
        var receiptSource = Encoding.UTF8.GetBytes(receiptText);
        return new DigestionAtom(
            0,
            receiptSource.Length,
            ImmutableArray.CreateRange(receiptSource),
            DigestionFingerprint.Compute(receiptSource),
            ImmutableArray<DigestionContext>.Empty);
    }

    private static DigestionReceipts CompleteWitnessReceipts(
        DigestionAtom atom,
        string gid,
        string definitionHash,
        string emissionHash) => new(
        [new DigestionCoverageReceipt(gid, atom.Fingerprints.RawSha256, TestModuleStatementId)],
        [new DigestionScribeReceipt(gid, definitionHash, emissionHash)],
        [],
        [],
        null);

    private static RawChangeSet StatusMoveChanges(string? atomId = null) =>
        RawChangeSet.CreateWithKinds(
    [
        (EntryPath(DigestionMigrationState.Partial, atomId), RawChangeKind.Deleted),
        (EntryPath(DigestionMigrationState.Absorbed, atomId), RawChangeKind.Added),
    ]);

    private static string EntryPath(
        DigestionMigrationState migration,
        string? atomId = null) =>
        BackfillInventoryLoader.RootPath
        + AtomizerRegistry.GictId
        + "/"
        + DigestionStatusNames.Migration(migration)
        + "-closed/"
        + (atomId ?? CompleteWitnessAtomId)
        + ".yaml";

    private static readonly string CompleteWitnessAtomId = DigestionFingerprint.Compute(
        Encoding.UTF8.GetBytes("manual specification receipt\n")).RawSha256["sha256:".Length..];
}
