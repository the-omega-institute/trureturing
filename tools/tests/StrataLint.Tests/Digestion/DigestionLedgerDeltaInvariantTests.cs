using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void TouchedPartialEntryRecomputesWhileUntouchedEntryKeepsBaselineMigration()
    {
        var receiptSource = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var currentSource = Encoding.UTF8.GetBytes("manual specification receipu\n");
        var atom = new DigestionAtom(
            0,
            receiptSource.Length,
            ImmutableArray.CreateRange(receiptSource),
            DigestionFingerprint.Compute(receiptSource),
            ImmutableArray<DigestionContext>.Empty);
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var document = Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed,
            gid,
            new DigestionCoverageReceipt(
                gid,
                atom.Fingerprints.RawSha256,
                TestModuleStatementId),
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
        var verifiedEmissions = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                gid,
                ScribeEmissionAttestation.DefinitionPath(gid),
                definitionHash,
                ScribeEmissionAttestation.EmissionPath(gid),
                emissionHash),
        ]);

        DigestionEntryEvaluation Evaluate(RawChangeSet changes) => Assert.Single(
            DigestionStatusEvaluator.Evaluate(
                DigestionEvaluationScope.ChangedSet,
                document,
                snapshot,
                AcceptedLean(targetPath),
                verifiedEmissions,
                baselineDocument: document,
                baselineSnapshot: snapshot,
                changes: changes).Entries);

        var outsideDelta = Evaluate(RawChangeSet.Create(["notes/unrelated.txt"]));
        var insideDelta = Evaluate(RawChangeSet.Create(
        [
            BackfillInventoryLoader.RootPath
                + $"{AtomizerRegistry.GictId}/partial-closed/"
                + atom.Fingerprints.RawSha256["sha256:".Length..]
                + ".yaml",
        ]));

        Assert.Equal(DigestionMigrationState.Partial, outsideDelta.DerivedStatus.Migration);
        Assert.Equal(DigestionMigrationState.Absorbed, insideDelta.DerivedStatus.Migration);
    }
}
