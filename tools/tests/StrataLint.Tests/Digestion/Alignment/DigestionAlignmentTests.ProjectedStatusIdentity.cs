using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void ChangedSetProjectedStatusPositionsHaveIdenticalAlignmentAndDerivation()
    {
        var fixture = ProjectedStatusIdentityFixture.Create();
        var baseline = fixture.WithStatus(
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed);
        var partial = fixture.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            baseline,
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed);
        var absorbed = fixture.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            baseline,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed);

        Assert.Equal(DigestionReceiptAlignment.Seen, partial.Alignment);
        Assert.Equal(DigestionReceiptAlignment.Seen, absorbed.Alignment);
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            partial.DerivedStatus);
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            absorbed.DerivedStatus);
        Assert.Equal(
        [
            new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Closed),
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
        ], fixture.EvaluatedStatuses);
    }

    [Fact]
    public void FullScanProjectedStatusPositionsHaveIdenticalAlignmentAndDerivation()
    {
        var fixture = ProjectedStatusIdentityFixture.Create();
        var baseline = fixture.WithStatus(
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed);
        var partial = fixture.Evaluate(
            DigestionEvaluationScope.FullScan,
            baseline,
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed);
        var absorbed = fixture.Evaluate(
            DigestionEvaluationScope.FullScan,
            baseline,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed);

        Assert.Equal(DigestionReceiptAlignment.Seen, partial.Alignment);
        Assert.Equal(DigestionReceiptAlignment.Seen, absorbed.Alignment);
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            partial.DerivedStatus);
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            absorbed.DerivedStatus);
        Assert.Equal(
        [
            new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Closed),
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
        ], fixture.EvaluatedStatuses);
    }

    [Fact]
    public void WrongProjectedStatusCannotSatisfyItsOwnFinalValidation()
    {
        var fixture = ProjectedStatusIdentityFixture.Create();
        var baseline = fixture.WithStatus(
            DigestionMigrationState.Residual,
            DigestionTruthState.Closed);
        var evaluation = fixture.EvaluateLedger(
            DigestionEvaluationScope.ChangedSet,
            baseline,
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed);

        Assert.Contains(
            evaluation.Findings,
            static finding => finding.Contains(
                "handwritten status partial-closed differs from derived absorbed-closed",
                StringComparison.Ordinal));
        Assert.True(evaluation.HasReceiptIntegrityFailure);
        var exception = Assert.Throws<InvalidOperationException>(() =>
            IngestCommand.RequireNoReceiptIntegrityFailure(evaluation));
        Assert.Contains("handwritten status", exception.Message, StringComparison.Ordinal);
    }

    private sealed record ProjectedStatusIdentityFixture(
        BackfillInventoryDocument Template,
        RepositorySnapshot Snapshot,
        AcceptedLeanClosure Lean,
        VerifiedScribeEmissions Verified)
    {
        private const string SourceId = "projected-status-identity";
        private const string TargetGid = "D5/S0/Carrier/ProjectedStatusIdentity";
        private const string TargetPath = "D5/S0/Carrier/ProjectedStatusIdentity.lean";

        internal List<DigestionStatus> EvaluatedStatuses { get; } = [];

        internal static ProjectedStatusIdentityFixture Create()
        {
            var sourceBytes = Encoding.UTF8.GetBytes(
                "# GICT\n\n**定理 1.1(A)**。projected status identity fixture。\n");
            var atomized = GictAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
            var atom = Assert.Single(atomized.Claims);
            var definition = Encoding.UTF8.GetBytes("scribe definition\n");
            var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
            var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
            var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
            var statementId = FrozenStatementReceiptTestData.Id('a');
            var entry = DigestionTestSupport.Entry(
                atom,
                AtomId(atom),
                AtomizerRegistry.GictId,
                DigestionMigrationState.Residual,
                DigestionTruthState.Closed,
                [TargetGid],
                new DigestionReceipts(
                    [new DigestionCoverageReceipt(TargetGid, atom.Fingerprints.RawSha256, statementId)],
                    [new DigestionScribeReceipt(TargetGid, definitionHash, emissionHash)],
                    [],
                    [],
                    null),
                sourceId: SourceId);
            var document = DigestionTestSupport.Document(
                AtomizerRegistry.GictId,
                [entry],
                sourceId: SourceId,
                genreRegistryCheck: atomized.GenreRegistryCheck);
            var record = new ScribeEmissionRecord(
                TargetGid,
                ScribeEmissionAttestation.DefinitionPath(TargetGid),
                definitionHash,
                ScribeEmissionAttestation.EmissionPath(TargetGid),
                emissionHash);
            var snapshot = DigestionTestSupport.Snapshot([
                ("docs/source.md", sourceBytes),
                DigestionTestSupport.CasFile(atom),
                (TargetPath, Encoding.UTF8.GetBytes(DigestionTestSupport.Lean(TargetGid))),
                (record.DefinitionPath, definition),
                (record.EmissionPath, emission),
                .. FrozenStatementReceiptTestData.LedgerFiles(
                    new FrozenStatementReceiptTestData.Module(TargetPath, statementId, [])),
            ]);
            return new ProjectedStatusIdentityFixture(
                document,
                snapshot,
                DigestionTestSupport.AcceptedLean(TargetPath),
                VerifiedScribeEmissions.Create([record]));
        }

        internal BackfillInventoryDocument WithStatus(
            DigestionMigrationState migration,
            DigestionTruthState truth)
        {
            var source = Assert.Single(Template.RequireDigestionSources());
            var entry = Assert.Single(source.Entries);
            return Template.WithDigestionSources(
            [
                source with
                {
                    Entries =
                    [
                        entry with
                        {
                            ProjectedStatus = new DigestionStatus(migration, truth),
                        },
                    ],
                },
            ]);
        }

        internal DigestionEntryEvaluation Evaluate(
            DigestionEvaluationScope scope,
            BackfillInventoryDocument? baseline,
            DigestionMigrationState migration,
            DigestionTruthState truth) => Assert.Single(
                EvaluateLedger(scope, baseline, migration, truth).Entries);

        internal DigestionLedgerEvaluation EvaluateLedger(
            DigestionEvaluationScope scope,
            BackfillInventoryDocument? baseline,
            DigestionMigrationState migration,
            DigestionTruthState truth)
        {
            EvaluatedStatuses.Add(new DigestionStatus(migration, truth));
            var changes = scope == DigestionEvaluationScope.ChangedSet
                ? RawChangeSet.Create(
                [
                    $"{BackfillInventoryLoader.RootPath}{SourceId}/source.toml",
                ])
                : null;
            return DigestionStatusEvaluator.Evaluate(
                scope,
                WithStatus(migration, truth),
                Snapshot,
                Lean,
                Verified,
                baseline,
                baselineSnapshot: baseline is null ? null : Snapshot,
                changes: changes);
        }
    }
}
