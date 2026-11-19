using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CheckRetainsStatusValidationWhenAxiomBadgeScribeByteReceiptDrifts()
    {
        var (outcome, verifier) = CheckReportDerivedScribeStockCore(
            reportInputsChanged: true,
            baselineHasScribeGap: false,
            baselineOnlyReportProducerInput: false,
            producerPathSetDiffers: false,
            handwrittenStatus: true);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(rejected.Diagnostics, static diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(6)
            && diagnostic.Path == "D5/S0/Carrier/BackfillTarget.lean"
            && diagnostic.Message.Contains("hand-written status", StringComparison.Ordinal));
        Assert.DoesNotContain(rejected.Diagnostics, static diagnostic =>
            diagnostic.Message.Contains("scribe-emission-mismatch", StringComparison.Ordinal));
        Assert.Equal(["std3"], verifier.AxiomBadges);
    }

    [Fact]
    public void CheckDoesNotReplayScribeMismatchAlreadyPresentInBaselineBytes()
    {
        var (outcome, verifier) = CheckReportDerivedScribeStock(
            reportInputsChanged: false,
            "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryLoader.cs");

        var protectedChange = RequireProtectedSurfaceChange(outcome);
        Assert.DoesNotContain(protectedChange.Observations, static diagnostic =>
            diagnostic.Message.Contains("scribe-emission-mismatch", StringComparison.Ordinal));
        Assert.Equal(["std3"], verifier.AxiomBadges);
    }

    [Fact]
    public void CheckDoesNotReplayBaselineOnlyProducerPathDrift()
    {
        var (outcome, verifier) = CheckBaselineOnlyReportProducerInputStock(
            "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryLoader.cs");

        var protectedChange = RequireProtectedSurfaceChange(outcome);
        Assert.DoesNotContain(protectedChange.Observations, static diagnostic =>
            diagnostic.Message.Contains("scribe-emission-mismatch", StringComparison.Ordinal));
        Assert.Equal(["std3"], verifier.AxiomBadges);
    }

    [Fact]
    public void CheckDoesNotReplayProducerPathSetBaselineDrift()
    {
        var (outcome, verifier) = CheckProducerPathSetsDifferStock(
            "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryLoader.cs");

        var protectedChange = RequireProtectedSurfaceChange(outcome);
        Assert.DoesNotContain(protectedChange.Observations, static diagnostic =>
            diagnostic.Message.Contains("scribe-emission-mismatch", StringComparison.Ordinal));
        Assert.Equal(["std3"], verifier.AxiomBadges);
    }

    [Fact]
    public void ProtectedSurfaceAdmissionCannotSkipProjectionReconciliationFailure()
    {
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());

        Assert.Throws<InvalidDataException>(() =>
            ProductionCliEnvironment.VerifyScribeForAdmission(
                new ProjectionReconciliationFailureVerifier(),
                RepositorySnapshot.Create([]),
                report, RawChangeSet.Create([])));
    }

    [Fact]
    public void CheckUsesCurrentProducerCapabilityDuringProtectedScribeGrowth()
    {
        var fixture = new RuleFixture();

        const string coveredDocumentGid = "D5/S0/Carrier/BackfillTarget";
        const string coveredGid = coveredDocumentGid + ".protectedTargetFixture";
        var targetPath = coveredDocumentGid + ".lean";
        var definitionPath = ScribeEmissionAttestation.DefinitionPath(coveredDocumentGid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(coveredDocumentGid);
        const string definition = "// previously verified Scribe definition\n";
        const string emission = "# Previously verified emission\n";
        var targetStatementId = FrozenStatementReceiptTestData.Id('b');
        var definitionHash = ("sha256:" + Trureturing.Truth.Sha256Sums.HashHex(Encoding.UTF8.GetBytes(definition)));
        var emissionHash = ("sha256:" + Trureturing.Truth.Sha256Sums.HashHex(Encoding.UTF8.GetBytes(emission)));
        var record = new ScribeEmissionRecord(
            coveredDocumentGid,
            definitionPath,
            definitionHash,
            emissionPath,
            emissionHash);
        var attestation = Encoding.UTF8.GetString(ScribeEmissionAttestation.Write([record]).AsSpan());
        fixture.Files[definitionPath] = definition;
        fixture.Baseline[definitionPath] = definition;
        fixture.Files[emissionPath] = emission;
        fixture.Baseline[emissionPath] = emission;
        fixture.Files[GeneratedArtifactInventory.ScribeAttestation.Path] = attestation;
        fixture.Baseline[GeneratedArtifactInventory.ScribeAttestation.Path] = attestation;
        var targetReport = new LeanFileReport(
            ImmutableArray<string>.Empty,
            [new LeanDeclaration(
                "protectedTargetFixture",
                "def",
                "Unit",
                ImmutableArray<string>.Empty)
            {
                NameKey = "ns(n0,22:protectedTargetFixture)",
                PrecomputedStatementId = targetStatementId,
            }]);
        fixture.Files[targetPath] = RuleFixture.HeaderFor(coveredDocumentGid, "F") + "def protectedTargetFixture : Unit := ()\n";
        fixture.Baseline[targetPath] = fixture.Files[targetPath];
        fixture.Reports[targetPath] = targetReport;
        fixture.BaselineReports[targetPath] = targetReport;
        var moduleStatementId = FrozenContentAddress.ComputeModuleStatementId(
            RepoPath.CreateKnown(targetPath),
            targetReport);
        AddFrozenTarget(fixture.Files, targetPath, moduleStatementId, targetReport);
        AddFrozenTarget(fixture.Baseline, targetPath, moduleStatementId, targetReport);
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
            currentReport, changes);

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

    }

    private static (AdmissionOutcome Outcome, ReportDerivedScribeEmissionVerifier Verifier)
        CheckReportDerivedScribeStock(bool reportInputsChanged, params string[] additionalChanges) =>
        CheckReportDerivedScribeStockCore(
            reportInputsChanged,
            baselineHasScribeGap: !reportInputsChanged,
            false,
            false,
            false,
            additionalChanges);

    private static AdmissionOutcome.ProtectedSurfaceChange RequireProtectedSurfaceChange(
        AdmissionOutcome outcome)
    {
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
        return Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
    }

    private static (AdmissionOutcome Outcome, ReportDerivedScribeEmissionVerifier Verifier)
        CheckBaselineOnlyReportProducerInputStock(params string[] additionalChanges) =>
        CheckReportDerivedScribeStockCore(false, false, true, false, false, additionalChanges);

    private static (AdmissionOutcome Outcome, ReportDerivedScribeEmissionVerifier Verifier)
        CheckProducerPathSetsDifferStock(params string[] additionalChanges) =>
        CheckReportDerivedScribeStockCore(false, false, false, true, false, additionalChanges);

    private static (AdmissionOutcome Outcome, ReportDerivedScribeEmissionVerifier Verifier)
        CheckReportDerivedScribeStockCore(
            bool reportInputsChanged,
            bool baselineHasScribeGap,
            bool baselineOnlyReportProducerInput,
            bool producerPathSetDiffers,
            bool handwrittenStatus,
            params string[] additionalChanges)
    {
        using var temporary = new TemporaryDirectory();
        const string documentGid = "D5/S0/Carrier/BackfillTarget";
        const string coverageGid = documentGid + ".protectedTargetFixture";
        const string targetPath = documentGid + ".lean";
        const string baselineDefinition = "fixture Scribe definition\n";
        const string baselineEmission = "# Fixture Scribe emission\n";
        var fixture = new RuleFixture();
        fixture.Files[targetPath] = RuleFixture.HeaderFor(documentGid, "F") + "def protectedTargetFixture : Unit := ()\n";


        var baselineTarget = fixture.Files[targetPath];
        fixture.Baseline[targetPath] = baselineTarget;
        var baselineDeclaration = new LeanDeclaration(
            "protectedTargetFixture",
            "def",
            "Unit",
            [])
        {
            NameKey = "ns(n0,22:protectedTargetFixture)",
            PrecomputedStatementId = FrozenStatementReceiptTestData.Id('b'),
        };
        var reportAxioms = ImmutableArray.Create("Classical.choice", "Quot.sound", "propext");
        fixture.Reports[targetPath] = new LeanFileReport(
            [],
            [baselineDeclaration with { Axioms = reportAxioms }]);
        var candidateTarget = baselineTarget.Replace(
            "def protectedTargetFixture : Unit := ()",
            "noncomputable def protectedTargetFixture : Unit := "
                + "Classical.choice (Nonempty.intro ())",
            StringComparison.Ordinal);
        Assert.NotEqual(baselineTarget, candidateTarget);
        if (handwrittenStatus)
        {
            candidateTarget += "-- status: proven\n";
        }
        fixture.Files[targetPath] = candidateTarget;
        if (!reportInputsChanged)
        {
            fixture.Baseline[targetPath] = candidateTarget;
        }
        fixture.BaselineReports[targetPath] = new LeanFileReport(
            [],
            [baselineDeclaration with { Axioms = reportInputsChanged ? [] : reportAxioms }]);
        var moduleStatementId = FrozenContentAddress.ComputeModuleStatementId(
            RepoPath.CreateKnown(targetPath),
            fixture.Reports[targetPath]);

        var definitionPath = ScribeEmissionAttestation.DefinitionPath(documentGid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(documentGid);
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[definitionPath] = baselineDefinition;
            files[emissionPath] = baselineEmission;
        }
        if (baselineOnlyReportProducerInput)
        {
            fixture.Baseline["tools/lean-inspector/baseline-only-input.txt"] =
                "baseline-only producer input\n";
        }
        if (producerPathSetDiffers)
        {
            fixture.Baseline["notes/baseline-producer-set-marker.txt"] =
                "baseline-only producer path-set marker\n";
        }

        var definitionSha256 = ("sha256:" + Trureturing.Truth.Sha256Sums.HashHex(Encoding.UTF8.GetBytes(baselineDefinition)));
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            AddFrozenTarget(files, targetPath, moduleStatementId, fixture.Reports[targetPath]);
        }

        var verifier = new ReportDerivedScribeEmissionVerifier(
            targetPath,
            coverageGid,
            documentGid,
            definitionSha256);
        var changes = (reportInputsChanged ? new[] { targetPath } : [])
            .Concat(additionalChanges)
            .ToArray();
        var currentRaw = Snapshot(fixture.Files);
        var baselineRaw = Snapshot(fixture.Baseline);
        var candidateReport = Path.Combine(temporary.Path, "candidate.json");
        RawLeanReportArtifact.WriteFile(
            candidateReport,
            Decode(currentRaw),
            LeanAxiomReport.Create(fixture.Reports));
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(changes),
                currentRaw,
                baselineRaw),
            new FakeLeanReportSource(null),
            verifier);

        return (
            environment.Check(["--candidate-lean-report", candidateReport]),
            verifier);

    }

    private static void AddFrozenTarget(
        IDictionary<string, string> files,
        string targetPath,
        StatementId moduleStatementId,
        LeanFileReport report) =>
        files[FrozenStatePath.FromModulePath(RepoPath.CreateKnown(targetPath)).Value] =
            Encoding.UTF8.GetString(FrozenStateRecord.Encode(
                moduleStatementId, FrozenStateRecord.Project(report)).AsSpan());

}

internal sealed class ProjectionReconciliationFailureVerifier : IScribeEmissionVerifier
{
    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes,
        FrozenStateCatalog? frozenState = null,
        FrozenStatementIndex? frozenStatements = null) =>
        throw new InvalidDataException("projection fixture/live-report disagreement");
}

internal sealed class ReportDerivedScribeEmissionVerifier(
    string targetPath,
    string coverageGid,
    string documentGid,
    string definitionSha256) : IScribeEmissionVerifier
{
    internal List<string> AxiomBadges { get; } = [];

    internal static string EmissionSha256For(IEnumerable<string> axioms)
    {
        var badge = AxiomBadge(axioms);
        return ("sha256:" + Trureturing.Truth.Sha256Sums.HashHex(Encoding.UTF8.GetBytes($"report-derived-axiom-badge:{badge}\n")));
    }

    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes,
        FrozenStateCatalog? frozenState = null,
        FrozenStatementIndex? frozenStatements = null)
    {
        var declaration = Assert.Single(report.Files[RepoPath.CreateKnown(targetPath)].Declarations);
        var badge = AxiomBadge(declaration.Axioms);
        AxiomBadges.Add(badge);
        return VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                documentGid,
                ScribeEmissionAttestation.DefinitionPath(documentGid),
                definitionSha256,
                ScribeEmissionAttestation.EmissionPath(documentGid),
                EmissionSha256For(declaration.Axioms)),
        ],
        [coverageGid]);
    }

    private static string AxiomBadge(IEnumerable<string> axioms) =>
        axioms.Any() ? "std3" : "constructive";
}
