using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// Split from ProductionEnvironmentTests.cs to keep that file under the SL-003 800-line
// limit (CapacityPolicyTests caught the growth in dotnet test). Same partial class.
public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void ProtectedSurfaceAdmissionCannotSkipProjectionReconciliationFailure()
    {
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());

        Assert.Throws<InvalidDataException>(() =>
            ProductionCliEnvironment.VerifyScribeForAdmission(
                new ProjectionReconciliationFailureVerifier(),
                RepositorySnapshot.Create([]),
                report));
    }

    [Fact]
    public void CheckUsesCurrentProducerCapabilityDuringProtectedScribeGrowth()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。covered。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, sourceBytes, DigestionTestSupport.Rules).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        const string coveredDocumentGid = "D5/S0/Carrier/BackfillTarget";
        const string coveredGid = coveredDocumentGid + ".protectedTargetFixture";
        var targetPath = coveredDocumentGid + ".lean";
        var definitionPath = ScribeEmissionAttestation.DefinitionPath(coveredDocumentGid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(coveredDocumentGid);
        const string definition = "// previously verified Scribe definition\n";
        const string emission = "# Previously verified emission\n";
        var targetHash = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(fixture.Files[targetPath])).RawSha256;
        var definitionHash = DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(definition)).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(emission)).RawSha256;
        var record = new ScribeEmissionRecord(
            coveredDocumentGid,
            definitionPath,
            definitionHash,
            emissionPath,
            emissionHash);
        var ledger = MapOnlyEntry(IngestLedger(atomizerId, atom), entry => entry with
        {
            CoverageGids = [coveredGid],
            Receipts = entry.Receipts with
            {
                Coverage =
                [
                    new DigestionCoverageReceipt(
                        coveredGid,
                        atom.Fingerprints.RawSha256,
                        targetHash),
                ],
                Scribe =
                [
                    new DigestionScribeReceipt(
                        coveredGid,
                        definitionHash,
                        emissionHash),
                ],
            },
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
        });
        var attestation = Encoding.UTF8.GetString(ScribeEmissionAttestation.Write([record]).AsSpan());
        var source = Encoding.UTF8.GetString(sourceBytes);
        var cas = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = source;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = source;
        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Baseline.Remove(RuleFixture.FixtureCasPath);
        fixture.Files[captured.RelativePath] = cas;
        fixture.Baseline[captured.RelativePath] = cas;
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, ledger);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, ledger);
        fixture.Files[definitionPath] = definition;
        fixture.Baseline[definitionPath] = definition;
        fixture.Files[emissionPath] = emission;
        fixture.Baseline[emissionPath] = emission;
        fixture.Files[ScribeEmissionAttestation.RelativePath] = attestation;
        fixture.Baseline[ScribeEmissionAttestation.RelativePath] = attestation;
        var targetReport = new LeanFileReport(
            ImmutableArray<string>.Empty,
            [new LeanDeclaration(
                "protectedTargetFixture",
                "def",
                "Unit",
                ImmutableArray<string>.Empty)]);
        fixture.Reports[targetPath] = targetReport;
        fixture.BaselineReports[targetPath] = targetReport;
        const string newScribePath = "Blueprint/D5/S0/Carrier/NewDeposit.scribe.cs";
        fixture.Files[newScribePath] = "// candidate-only Scribe definition\n";
        var current = Decode(Snapshot(fixture.Files));
        var baseline = Decode(Snapshot(fixture.Baseline));
        var currentReport = LeanAxiomReport.Create(fixture.Reports);
        var changes = RawChangeSet.Create([newScribePath]);
        var bootstrap = BootstrapGate.Evaluate(changes);
        var verifiedScribeEmissions = ProductionCliEnvironment.VerifyScribeForAdmission(
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Create([record], [coveredGid])),
            current,
            currentReport);

        var outcome = SnapshotAdmissionCore.Evaluate(
            current,
            baseline,
            currentReport,
            changes,
            bootstrap,
            verifiedScribeEmissions).Outcome;

        Assert.True(
            outcome is AdmissionOutcome.ProtectedSurfaceChange,
            outcome switch
            {
                AdmissionOutcome.RuleRejected rejected => string.Join(
                    '\n',
                    rejected.Diagnostics.Select(static diagnostic => diagnostic.Render())),
                AdmissionOutcome.InfrastructureFailure failure => failure.Message,
                _ => outcome.GetType().FullName,
            });

        var baselineDocument = ledger;
        var currentLean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(current, currentReport)).Capability;
        var currentStatus = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            baselineDocument,
            current,
            currentLean,
            verifiedScribeEmissions,
            baselineDocument).Entries);
        Assert.Equal(DigestionMigrationState.Absorbed, currentStatus.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, currentStatus.DerivedStatus.Truth);
        Assert.True(currentStatus.Deletable);
        Assert.Empty(currentStatus.Gaps);

        const string changedEmission = "# Candidate changed a previously verified emission\n";
        var changedEmissionHash = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(changedEmission)).RawSha256;
        var changedLedger = MapOnlyEntry(ledger, entry => entry with
        {
            Receipts = entry.Receipts with
            {
                Scribe = entry.Receipts.Scribe.Select(receipt => receipt with
                {
                    EmissionSha256 = changedEmissionHash,
                }).ToImmutableArray(),
            },
        });
        var changedFiles = new Dictionary<string, string>(fixture.Files, StringComparer.Ordinal)
        {
            [emissionPath] = changedEmission,
            [ScribeEmissionAttestation.RelativePath] = Encoding.UTF8.GetString(
                ScribeEmissionAttestation.Write(
                [
                    record with { EmissionSha256 = changedEmissionHash },
                ]).AsSpan()),
        };
        DirectoryLedgerTestSupport.ReplaceWithProjection(changedFiles, changedLedger);
        var changedSnapshot = Decode(Snapshot(changedFiles));
        var changedLean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(changedSnapshot, currentReport)).Capability;
        var changedStatus = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            BackfillInventoryLoader.Load(changedSnapshot),
            changedSnapshot,
            changedLean,
            verifiedScribeEmissions,
            baselineDocument).Entries);
        Assert.Equal(DigestionMigrationState.Partial, changedStatus.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, changedStatus.DerivedStatus.Truth);
        Assert.False(changedStatus.Deletable);
        Assert.Contains(changedStatus.Gaps, gap => gap.Code == "scribe-emission-mismatch");
    }
}

internal sealed class ProjectionReconciliationFailureVerifier : IScribeEmissionVerifier
{
    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes = null) =>
        throw new InvalidDataException("projection fixture/live-report disagreement");
}
