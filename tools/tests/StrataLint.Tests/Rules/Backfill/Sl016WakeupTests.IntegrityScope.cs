using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class Sl016WakeupTests
{
    [Fact]
    public void HarmlessLeanCommentDoesNotRepublishHistoricalDeclarationReferenceGapButDefinitionChangeDoes()
    {
        var harmless = MissingDeclarationReferenceContext(definitionChanged: false);
        var harmlessDocument = BackfillInventoryLoader.LoadCandidateDelta(
            harmless.Current,
            harmless.Baseline,
            harmless.Changes);
        var harmlessEntry = Assert.Single(harmlessDocument.RequireDigestionEntries());
        var harmlessCoverage = Assert.Single(harmlessEntry.Coverage);
        var harmlessEdge = CurrentEdgeValidator.Validate(
            harmlessCoverage.Gid,
            harmless.Current,
            harmless.Lean.Report,
            LeanTruthStates.Resolve(harmless.Current, harmless.Lean),
            FrozenStatementIndex.Create(
                FrozenStateCatalog.Load(harmless.Current),
                harmless.Lean.Report));
        var harmlessImpact = BackfillDeltaImpactResolver.Resolve(
            harmless.Current,
            harmless.Baseline,
            harmless.Lean.Report,
            harmlessDocument,
            harmless.Changes);
        var harmlessOutcome = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(harmless)).Capability;

        Assert.True(harmlessEdge.IsResolved, harmlessEdge.Diagnostic);
        Assert.True(harmlessEdge.IsClosed, harmlessEdge.Diagnostic);
        Assert.Equal(harmlessCoverage.TargetStatementId, harmlessEdge.TargetStatementId);
        Assert.False(harmlessImpact.HasAffectedEdges);
        Assert.Empty(harmlessImpact.EvaluationChanges.Paths);
        Assert.DoesNotContain(harmlessOutcome.Diagnostics, static finding =>
            finding.RuleId == RuleId.CreateKnown(16)
            && finding.Message.Contains(
                "scribe-declaration-reference-missing",
                StringComparison.Ordinal));

        var changed = MissingDeclarationReferenceContext(definitionChanged: true);
        var changedDocument = BackfillInventoryLoader.LoadCandidateDelta(
            changed.Current,
            changed.Baseline,
            changed.Changes);
        var changedImpact = BackfillDeltaImpactResolver.Resolve(
            changed.Current,
            changed.Baseline,
            changed.Lean.Report,
            changedDocument,
            changed.Changes);
        var changedOutcome = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(changed)).Capability;

        Assert.True(changedImpact.HasAffectedEdges);
        Assert.Contains(changedImpact.EvaluationChanges.Paths, static path => path.Value == AtomPath);
        var blocking = Assert.Single(changedOutcome.Diagnostics, static finding =>
            finding.RuleId == RuleId.CreateKnown(16)
            && finding.Message.Contains(
                "scribe-declaration-reference-missing",
                StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, blocking.AdmissionEffect);
    }

    [Theory]
    [InlineData("invalid-header")]
    [InlineData("pending-state")]
    [InlineData("mixed-open-closed-to-pending")]
    [InlineData("mixed-open-pending-to-closed")]
    public void LeanApplicabilityChangeWithStableTargetValueWakesAndJudgesReferencedEdge(
        string scenario)
    {
        const string targetGid = "D5/S0/Carrier/BackfillTarget";
        var targetPath = targetGid + ".lean";
        var fixture = CoverageReceiptFixture(
            targetGid,
            FrozenStatementReceiptTestData.Id('a'));
        var changedPaths = new List<string> { targetPath };
        var mixedOpen = scenario.StartsWith("mixed-open-", StringComparison.Ordinal);
        if (scenario == "invalid-header")
        {
            fixture.Files[targetPath] = fixture.Files[targetPath].Replace(
                "none(waiver:test-fixture)",
                "none(waiver: )",
                StringComparison.Ordinal);
        }
        else
        {
            if (!mixedOpen)
            {
                var closedAtomPath = AtomPath.Replace(
                    "partial-open", "partial-closed", StringComparison.Ordinal);
                foreach (var files in new[] { fixture.Files, fixture.Baseline })
                {
                    files[closedAtomPath] = files[AtomPath];
                    files.Remove(AtomPath);
                }
            }

            fixture.Files[targetPath] += "\n-- candidate proof authority changed\n";
            if (scenario == "mixed-open-pending-to-closed")
            {
                var statePath = FrozenStatePath.FromModulePath(RepoPath.CreateKnown(targetPath)).Value;
                fixture.Baseline.Remove(statePath);
                changedPaths.Add(statePath);
            }
            else
            {
                fixture.Reports[targetPath] = new LeanFileReport([], [new LeanDeclaration(
                    "protectedTargetFixture", "def", "Unit", ["fixture.nonstandard"])]);
            }
        }

        if (mixedOpen)
        {
            foreach (var files in new[] { fixture.Files, fixture.Baseline })
            {
                files[AtomPath] = files[AtomPath].Replace(
                    "receipts:\n",
                    "  - gid: D5/X_Frontier/Hearts\n"
                        + "    target_statement_id: null\n"
                        + "receipts:\n",
                    StringComparison.Ordinal);
            }
        }

        var context = fixture.Build(RawChangeSet.Create(changedPaths));
        var ruleEvaluation = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context)).Capability;
        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);
        var impact = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            context.Lean.Report,
            document,
            context.Changes);
        var entry = Assert.Single(document.RequireDigestionEntries());

        Assert.True(impact.HasAffectedEdges);
        Assert.True(DigestionCasStore.EntryChanged(entry, impact.EvaluationChanges));
        if (scenario == "invalid-header")
        {
            Assert.Contains(
                ruleEvaluation.Diagnostics,
                static finding => finding.Message.Contains(
                    "scribe-applicability-invalid",
                    StringComparison.Ordinal));
        }

        if (mixedOpen)
        {
            var evaluation = DigestionStatusEvaluator.Evaluate(
                DigestionEvaluationScope.ChangedSet,
                document,
                context.Current,
                context.Lean,
                context.VerifiedScribeEmissions,
                BackfillInventoryLoader.LoadBaseline(context.Baseline),
                baselineSnapshot: context.Baseline,
                changes: impact.EvaluationChanges,
                projectedStatusChanges: impact.EvaluationChanges);
            var expectedObservation = scenario == "mixed-open-closed-to-pending"
                ? "scribe-pending-target"
                : "scribe-not-applicable:mirror-waiver";

            Assert.Contains(
                Assert.Single(evaluation.Entries).ReceiptObservations,
                observation => observation.Code == expectedObservation);
        }
    }

    [Fact]
    public void MalformedChangedAuthorityRemainsBlockingAtSl016Admission()
    {
        const string targetGid = "D5/S0/Carrier/BackfillTarget";
        var targetPath = targetGid + ".lean";
        var fixture = CoverageReceiptFixture(
            targetGid,
            FrozenStatementReceiptTestData.Id('a'));
        var statePath = FrozenStatePath.FromModulePath(RepoPath.CreateKnown(targetPath)).Value;
        fixture.Files[statePath] = "{}";
        var context = fixture.Build(RawChangeSet.Create([statePath]));

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context)).Capability;

        var diagnostic = Assert.Single(completed.Diagnostics, static finding =>
            finding.RuleId == RuleId.CreateKnown(16)
            && finding.Message.Contains("scribe-applicability-invalid", StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    private static RuleEvaluationContext MissingDeclarationReferenceContext(bool definitionChanged)
    {
        const string documentGid = "D5/S0/Carrier/BackfillTarget";
        const string coverageGid = documentGid + ".protectedTargetFixture";
        const string targetPath = documentGid + ".lean";
        const string baselineDefinition = "fixture Scribe definition\n";
        const string changedDefinition = "changed fixture Scribe definition\n";
        const string emission = "# Fixture Scribe emission\n";
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.UseValidDirectoryBackfill();
        InstallFrozenModules(fixture, documentGid);
        fixture.Reports[targetPath] = new LeanFileReport(
            [],
            [new LeanDeclaration("protectedTargetFixture", "def", "Unit", [])
                { NameKey = "ns(n0,22:protectedTargetFixture)" }]);
        fixture.Baseline[targetPath] = fixture.Files[targetPath];
        fixture.BaselineReports[targetPath] = fixture.Reports[targetPath];

        var definitionPath = ScribeEmissionAttestation.DefinitionPath(documentGid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(documentGid);
        var baselineDefinitionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(baselineDefinition)).RawSha256;
        var candidateDefinition = definitionChanged ? changedDefinition : baselineDefinition;
        var candidateDefinitionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(candidateDefinition)).RawSha256;
        var emissionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(emission)).RawSha256;
        var targetStatementId = Assert.Single(CanonicalStatementWriter.DeclarationStatementIds(
            RepoPath.CreateKnown(targetPath),
            fixture.Reports[targetPath])).StatementId.Value;
        var receiptProjection = "coverage_gids:\n"
            + $"  - gid: {coverageGid}\n"
            + $"    target_statement_id: {targetStatementId}\n"
            + "receipts:\n"
            + "  scribe:\n"
            + $"    - gid: {coverageGid}\n"
            + $"      definition_sha256: {baselineDefinitionSha256}\n"
            + $"      emission_sha256: {emissionSha256}";
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[definitionPath] = baselineDefinition;
            files[emissionPath] = emission;
            files[AtomPath] = AddReceipts(files[AtomPath], receiptProjection);
        }

        fixture.Files[targetPath] += "\n-- harmless non-TASK comment\n";
        fixture.Files[definitionPath] = candidateDefinition;
        var verified = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                documentGid,
                definitionPath,
                candidateDefinitionSha256,
                emissionPath,
                emissionSha256),
        ]);
        var changes = definitionChanged
            ? RawChangeSet.Create([targetPath, definitionPath])
            : RawChangeSet.Create([targetPath]);
        return fixture.Build(changes, verifiedScribeEmissions: verified);
    }
}
