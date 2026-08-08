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
        var bootstrap = BootstrapGate.Evaluate(RawChangeSet.Create([
            RuleFixture.SyntheticProtectedPath,
        ]));

        Assert.Throws<InvalidDataException>(() =>
            ProductionCliEnvironment.VerifyScribeForAdmission(
                new ProjectionReconciliationFailureVerifier(),
                report,
                bootstrap));
    }

    [Fact]
    public void CheckPreservesPriorCoverageWhenProtectedScribeGrowthOutrunsBaseEmitter()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var canonicalLedger = fixture.Files["Meta/BACKFILL.yaml"];
        var ticketIndex = canonicalLedger[canonicalLedger.IndexOf("ticket_index:", StringComparison.Ordinal)..];
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
        var ledger = IngestLedger(atomizerId, atom)
            .Replace(
                "        coverage_gids: []",
                $"        coverage_gids:\n          - {coveredGid}",
                StringComparison.Ordinal)
            .Replace(
                "          coverage: []",
                $$"""
                          coverage:
                            - gid: {{coveredGid}}
                              source_sha256: {{atom.Fingerprints.RawSha256}}
                              target_sha256: {{targetHash}}
                """,
                StringComparison.Ordinal)
            .Replace(
                "          scribe: []",
                $$"""
                          scribe:
                            - gid: {{coveredGid}}
                              definition_sha256: {{definitionHash}}
                              emission_sha256: {{emissionHash}}
                """,
                StringComparison.Ordinal)
            .Replace("          migration: residual", "          migration: absorbed", StringComparison.Ordinal)
            .Replace("          truth: open", "          truth: closed", StringComparison.Ordinal)
            .Replace("ticket_index: []", ticketIndex, StringComparison.Ordinal);
        var attestation = Encoding.UTF8.GetString(ScribeEmissionAttestation.Write([record]).AsSpan());
        var source = Encoding.UTF8.GetString(sourceBytes);
        var cas = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = source;
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = source;
        fixture.Files.Remove(GoldenCorpus.FixtureCasPath);
        fixture.Baseline.Remove(GoldenCorpus.FixtureCasPath);
        fixture.Files[captured.RelativePath] = cas;
        fixture.Baseline[captured.RelativePath] = cas;
        fixture.Files["Meta/BACKFILL.yaml"] = ledger;
        fixture.Baseline["Meta/BACKFILL.yaml"] = ledger;
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
        var baselineReport = LeanAxiomReport.Create(fixture.BaselineReports);
        var changes = RawChangeSet.Create([newScribePath]);
        var bootstrap = BootstrapGate.Evaluate(changes);
        var verifiedScribeEmissions = ProductionCliEnvironment.VerifyScribeForAdmission(
            new FakeScribeEmissionVerifier(null),
            currentReport,
            bootstrap);

        var outcome = SnapshotAdmissionCore.Evaluate(
            current,
            baseline,
            currentReport,
            baselineReport,
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

        var baselineDocument = BackfillInventoryLoader.Load(ledger);
        var currentLean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(current, currentReport)).Capability;
        var currentStatus = Assert.Single(DigestionStatusEvaluator.Evaluate(
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
        var changedFiles = new Dictionary<string, string>(fixture.Files, StringComparer.Ordinal)
        {
            ["Meta/BACKFILL.yaml"] = ledger.Replace(
                emissionHash,
                changedEmissionHash,
                StringComparison.Ordinal),
            [emissionPath] = changedEmission,
            [ScribeEmissionAttestation.RelativePath] = Encoding.UTF8.GetString(
                ScribeEmissionAttestation.Write(
                [
                    record with { EmissionSha256 = changedEmissionHash },
                ]).AsSpan()),
        };
        var changedSnapshot = Decode(Snapshot(changedFiles));
        var changedLean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(changedSnapshot, currentReport)).Capability;
        var changedStatus = Assert.Single(DigestionStatusEvaluator.Evaluate(
            BackfillInventoryLoader.Load(changedFiles["Meta/BACKFILL.yaml"]),
            changedSnapshot,
            changedLean,
            verifiedScribeEmissions,
            baselineDocument).Entries);
        Assert.Equal(DigestionMigrationState.Partial, changedStatus.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, changedStatus.DerivedStatus.Truth);
        Assert.False(changedStatus.Deletable);
        Assert.Contains(changedStatus.Gaps, gap => gap.Code == "scribe-emission-unverified");
    }
}

internal sealed class ProjectionReconciliationFailureVerifier : IScribeEmissionVerifier
{
    public VerifiedScribeEmissions Verify(LeanAxiomReport report) =>
        throw new InvalidDataException("projection fixture/live-report disagreement");
}
