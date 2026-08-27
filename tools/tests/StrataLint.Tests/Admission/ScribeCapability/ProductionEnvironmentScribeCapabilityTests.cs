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
    public void CheckBlocksNewAxiomBadgeScribeMismatchAbsentFromBaselineBytes()
    {
        var (outcome, verifier) = CheckReportDerivedScribeStock(reportInputsChanged: true);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var mismatch = Assert.Single(rejected.Diagnostics, static diagnostic =>
            diagnostic.Message.Contains("scribe-emission-mismatch", StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, mismatch.AdmissionEffect);
        Assert.Equal(["std3"], verifier.AxiomBadges);
    }

    [Fact]
    public void CheckBlocksScribeMismatchAlreadyPresentInBaselineBytes()
    {
        var (outcome, verifier) = CheckReportDerivedScribeStock(
            reportInputsChanged: false,
            "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs");

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var mismatch = Assert.Single(rejected.Diagnostics, static diagnostic =>
            diagnostic.Message.Contains("scribe-emission-mismatch", StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, mismatch.AdmissionEffect);
        Assert.Equal(["std3"], verifier.AxiomBadges);
    }

    [Fact]
    public void CheckBlocksForkOnlyProducerPathCounterexampleViaBaselineDriftComparison()
    {
        var (outcome, verifier) = CheckForkPointOnlyReportProducerInputStock(
            "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs");

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var mismatch = Assert.Single(rejected.Diagnostics, static diagnostic =>
            diagnostic.Message.Contains("scribe-emission-mismatch", StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, mismatch.AdmissionEffect);
        Assert.Equal(["std3"], verifier.AxiomBadges);
    }

    [Fact]
    public void CheckBlocksProducerPathSetCounterexampleViaBaselineDriftComparison()
    {
        var (outcome, verifier) = CheckProducerPathSetsDifferStock(
            "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs");

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var mismatch = Assert.Single(rejected.Diagnostics, static diagnostic =>
            diagnostic.Message.Contains("scribe-emission-mismatch", StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, mismatch.AdmissionEffect);
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
        var targetStatementId = FrozenStatementReceiptTestData.Id('b');
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
                        targetStatementId),
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
        AddFrozenTarget(fixture.Files, targetPath);
        AddFrozenTarget(fixture.Baseline, targetPath);
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

    private static (AdmissionOutcome Outcome, ReportDerivedScribeEmissionVerifier Verifier)
        CheckReportDerivedScribeStock(bool reportInputsChanged, params string[] additionalChanges) =>
        CheckReportDerivedScribeStockCore(
            reportInputsChanged,
            baselineHasScribeGap: !reportInputsChanged,
            false,
            false,
            additionalChanges);

    private static (AdmissionOutcome Outcome, ReportDerivedScribeEmissionVerifier Verifier)
        CheckForkPointOnlyReportProducerInputStock(params string[] additionalChanges) =>
        CheckReportDerivedScribeStockCore(false, false, true, false, additionalChanges);

    private static (AdmissionOutcome Outcome, ReportDerivedScribeEmissionVerifier Verifier)
        CheckProducerPathSetsDifferStock(params string[] additionalChanges) =>
        CheckReportDerivedScribeStockCore(false, false, false, true, additionalChanges);

    private static (AdmissionOutcome Outcome, ReportDerivedScribeEmissionVerifier Verifier)
        CheckReportDerivedScribeStockCore(
            bool reportInputsChanged,
            bool baselineHasScribeGap,
            bool forkPointOnlyReportProducerInput,
            bool producerPathSetDiffers,
            params string[] additionalChanges)
    {
        using var temporary = new TemporaryDirectory();
        const string atomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        const string documentGid = "D5/S0/Carrier/BackfillTarget";
        const string coverageGid = documentGid + ".protectedTargetFixture";
        const string targetPath = documentGid + ".lean";
        const string baselineDefinition = "fixture Scribe definition\n";
        const string baselineEmission = "# Fixture Scribe emission\n";
        var fixture = new RuleFixture();
        fixture.UseValidDirectoryBackfill();
        fixture.AddBackfillTargets();

        var baselineTarget = fixture.Files[targetPath];
        fixture.Baseline[targetPath] = baselineTarget;
        fixture.ForkPoint[targetPath] = baselineTarget;
        var baselineDeclaration = new LeanDeclaration(
            "protectedTargetFixture",
            "def",
            "Unit",
            []);
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
        fixture.Files[targetPath] = candidateTarget;
        if (!reportInputsChanged)
        {
            fixture.Baseline[targetPath] = candidateTarget;
            fixture.ForkPoint[targetPath] = candidateTarget;
        }
        fixture.BaselineReports[targetPath] = new LeanFileReport(
            [],
            [baselineDeclaration with { Axioms = reportInputsChanged ? [] : reportAxioms }]);

        var definitionPath = ScribeEmissionAttestation.DefinitionPath(documentGid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(documentGid);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[definitionPath] = baselineDefinition;
            files[emissionPath] = baselineEmission;
        }
        if (forkPointOnlyReportProducerInput)
        {
            fixture.ForkPoint["tools/lean-inspector/fork-only-input.txt"] =
                "fork-only producer input\n";
        }
        if (producerPathSetDiffers)
        {
            fixture.ForkPoint["notes/fork-producer-set-marker.txt"] =
                "fork-only producer path-set marker\n";
        }

        var definitionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(baselineDefinition)).RawSha256;
        var stockEmissionSha256 = baselineHasScribeGap
            ? ReportDerivedScribeEmissionVerifier.EmissionSha256For([])
            : DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(baselineEmission)).RawSha256;
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            AddFrozenTarget(files, targetPath);
            InstallLedger(files);
        }

        var verifier = new ReportDerivedScribeEmissionVerifier(
            targetPath,
            coverageGid,
            documentGid,
            definitionSha256);
        var changes = (reportInputsChanged ? new[] { atomPath, targetPath } : [])
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
                baselineRaw,
                forkPoint: forkPointOnlyReportProducerInput || producerPathSetDiffers
                    ? Snapshot(fixture.ForkPoint)
                    : null),
            new FakeLeanReportSource(null),
            verifier,
            new NoOpFrozenLedgerAdmissionServices());

        return (
            environment.Check(["--candidate-lean-report", candidateReport]),
            verifier);

        void InstallLedger(Dictionary<string, string> files)
        {
            var document = BackfillInventoryLoader.Load(Decode(Snapshot(files)));
            document = MapOnlyEntry(document, entry => entry with
            {
                CoverageGids = [coverageGid],
                Receipts = entry.Receipts with
                {
                    Coverage =
                    [
                        new DigestionCoverageReceipt(
                            coverageGid,
                            entry.Fingerprints.RawSha256,
                            FrozenStatementReceiptTestData.Id('b')),
                    ],
                    Scribe =
                    [
                        new DigestionScribeReceipt(
                            coverageGid,
                            definitionSha256,
                            stockEmissionSha256),
                    ],
                },
            });
            DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        }

    }

    private static void AddFrozenTarget(
        IDictionary<string, string> files,
        string targetPath) =>
        FrozenStatementReceiptTestData.AddLedger(
            files,
            new FrozenStatementReceiptTestData.Module(
                targetPath,
                FrozenStatementReceiptTestData.Id('a'),
                [
                    new FrozenStatementReceiptTestData.Declaration(
                        "protectedTargetFixture",
                        FrozenStatementReceiptTestData.Id('b')),
                ]));
}

internal sealed class ProjectionReconciliationFailureVerifier : IScribeEmissionVerifier
{
    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes = null) =>
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
        return DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes($"report-derived-axiom-badge:{badge}\n")).RawSha256;
    }

    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes = null)
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

internal sealed class NoOpFrozenLedgerAdmissionServices : IFrozenLedgerAdmissionServices
{
    public IReadOnlySet<string> LeanReportProducerPaths { get; } =
        ImmutableHashSet<string>.Empty;

    public FrozenLedgerAdmissionPreparation Prepare(
        RepositorySnapshot current,
        RepositorySnapshot protectedBase,
        RawChangeSet changes,
        Func<FrozenLedgerReferenceSet, TrustedFrozenGitReferences> validateReferences) => null!;

    public AdmissionOutcome? Validate(
        FrozenLedgerAdmissionPreparation preparation,
        RepositorySnapshot current,
        AcceptedLeanClosure lean,
        LeanAxiomReport report,
        RawChangeSet changes,
        FrozenRevisionIdentity currentIdentity,
        AdmissionCheckTiming timing) => null;
}
