using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void CrossSourceChainGapTracksChildAbsorptionAtGlobalIdentity()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("cross-source chain status\n");
        var atom = new DigestionAtom(
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            ImmutableArray<DigestionContext>.Empty);
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        const string childId = "cross-source-child";
        const string parentId = "cross-source-parent";
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var template = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            gid,
            new DigestionCoverageReceipt(
                gid,
                atom.Fingerprints.RawSha256,
                TestModuleStatementId),
            new DigestionScribeReceipt(gid, definitionHash, emissionHash),
            atomizer: AtomizerRegistry.NoAtomizerId);
        var source = Assert.Single(template.RequireDigestionSources());
        var completeEntry = Assert.Single(source.Entries);
        var completeChild = completeEntry with
        {
            SourceId = "child-source",
            SourcePath = "docs/child-source.md",
            AtomId = childId,
        };
        var incompleteChild = completeChild with
        {
            CoverageGids = [],
            Receipts = new DigestionReceipts([], [], [], [], null),
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Residual,
                DigestionTruthState.Open),
        };
        var completeParent = completeEntry with
        {
            SourceId = "parent-source",
            SourcePath = "docs/parent-source.md",
            AtomId = parentId,
            Receipts = completeEntry.Receipts with { ChainAtoms = [childId] },
        };
        var incompleteParent = completeParent with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Closed),
        };
        BackfillInventoryDocument Document(
            DigestionLedgerEntry child,
            DigestionLedgerEntry parent) => template.WithDigestionSources(
        [
            source with
            {
                SourceId = "child-source",
                SourcePath = "docs/child-source.md",
                Entries = [child],
            },
            source with
            {
                SourceId = "parent-source",
                SourcePath = "docs/parent-source.md",
                Entries = [parent],
            },
        ]);
        var incompleteDocument = Document(incompleteChild, incompleteParent);
        var completeDocument = Document(completeChild, completeParent);
        var record = new ScribeEmissionRecord(
            gid,
            ScribeEmissionAttestation.DefinitionPath(gid),
            definitionHash,
            ScribeEmissionAttestation.EmissionPath(gid),
            emissionHash);
        var snapshot = Snapshot([
            ("docs/child-source.md", sourceBytes),
            ("docs/parent-source.md", sourceBytes),
            CasFile(atom),
            (targetPath, target),
            (record.DefinitionPath, definition),
            (record.EmissionPath, emission),
            .. FrozenLedgerFiles(targetPath, "probe"),
        ]);

        var incompleteEvaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            incompleteDocument,
            snapshot,
            AcceptedLean(targetPath),
            VerifiedScribeEmissions.Create([record]),
            baselineDocument: incompleteDocument);
        var completeEvaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            completeDocument,
            snapshot,
            AcceptedLean(targetPath),
            VerifiedScribeEmissions.Create([record]),
            baselineDocument: completeDocument);

        var unresolvedParent = Assert.Single(
            incompleteEvaluation.Entries,
            static entry => entry.Entry.AtomId == parentId);
        Assert.NotEqual(
            DigestionMigrationState.Absorbed,
            unresolvedParent.DerivedStatus.Migration);
        Assert.Contains(unresolvedParent.Gaps, static gap =>
            gap.Code == "chain-migration-incomplete" && gap.Detail == childId);
        var resolvedParent = Assert.Single(
            completeEvaluation.Entries,
            static entry => entry.Entry.AtomId == parentId);
        Assert.Equal(
            DigestionMigrationState.Absorbed,
            resolvedParent.DerivedStatus.Migration);
        Assert.DoesNotContain(resolvedParent.Gaps, static gap =>
            gap.Code == "chain-migration-incomplete");
    }
}
