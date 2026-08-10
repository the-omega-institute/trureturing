using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class ConservativeActualTreeEvaluator
{
    internal static ConservativeCaseResult EvaluateBaselineTree(
        ConservativeHarnessInvocation invocation)
    {
        var repository = new GitRepositoryGateway(invocation.BaselineRoot);
        var snapshot = Decode(repository.ReadRevision(invocation.BaselineIdentity.CommitOid));
        var report = RawLeanReportArtifact.ReadFile(invocation.BaselineLeanReport, snapshot);
        var candidateChanges = new GitRepositoryGateway(invocation.CandidateRoot)
            .Prepare(invocation.BaselineIdentity.CommitOid).Changes;
        var verifiedScribe = VerifyBaselineScribeForReplay(
            new ProductionScribeEmissionVerifier(invocation.BaselineRoot),
            report,
            candidateChanges);
        var changes = RawChangeSet.Create(Array.Empty<string>());
        var evaluation = SnapshotAdmissionCore.Evaluate(
            snapshot,
            snapshot,
            report,
            report,
            changes,
            BootstrapGate.Evaluate(changes),
            verifiedScribe);
        var admission = evaluation.Outcome;
        if (admission is AdmissionOutcome.Admitted)
        {
            if (evaluation is not
                {
                    CurrentLean: { } lean,
                    BaselineLean: { } baselineLean,
                    CurrentDag: { } dag,
                    BaselineDag: { } baselineDag,
                })
            {
                throw new InvalidOperationException(
                    "baseline actual admission omitted frozen-ledger capabilities");
            }

            admission = ProductionFrozenLedgerValidator.Validate(
                    snapshot,
                    snapshot,
                    lean,
                    baselineLean,
                    dag,
                    baselineDag,
                    repository)
                ?? admission;
        }

        return Result(
            ConservativeExtensionCommand.BaseTreeCaseId,
            BaseTreeCaseRoot(invocation),
            admission);
    }

    internal static ConservativeCaseResult EvaluateCandidateTree(
        ConservativeHarnessInvocation invocation)
    {
        var admission = new ProductionCliEnvironment(invocation.CandidateRoot).Check(
        [
            "--protected-base", invocation.BaselineIdentity.CommitOid,
            "--candidate-lean-report", invocation.CandidateLeanReport,
            "--baseline-lean-report", invocation.BaselineLeanReport,
            "--frozen-evidence-root", invocation.BaselineRoot,
        ]);
        return Result(
            ConservativeExtensionCommand.CandidateTreeCaseId,
            CandidateTreeCaseRoot(invocation),
            admission);
    }

    internal static VerifiedScribeEmissions? VerifyBaselineScribeForReplay(
        IScribeEmissionVerifier verifier,
        LeanAxiomReport report,
        RawChangeSet candidateChanges)
    {
        ArgumentNullException.ThrowIfNull(verifier);
        ArgumentNullException.ThrowIfNull(report);
        ArgumentNullException.ThrowIfNull(candidateChanges);
        var bootstrap = BootstrapGate.Evaluate(candidateChanges);
        if (bootstrap is BootstrapOutcome.InfrastructureFailure failure)
        {
            throw new InvalidOperationException(failure.Message);
        }

        return ProductionCliEnvironment.VerifyScribeForAdmission(
            verifier,
            report,
            bootstrap);
    }

    private static ConservativeCaseResult Result(
        string caseId,
        string caseRoot,
        AdmissionOutcome outcome)
    {
        var diagnostics = outcome switch
        {
            AdmissionOutcome.RuleRejected rejected => rejected.Diagnostics,
            AdmissionOutcome.ProtectedSurfaceVerificationRequired verification =>
                verification.Diagnostics,
            AdmissionOutcome.ProtectedSurfaceChange protectedChange =>
                protectedChange.Sl022Diagnostics,
            AdmissionOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(
                    $"actual tree infrastructure failure: {failure.Message}"),
            AdmissionOutcome.Admitted => ImmutableArray<Diagnostic>.Empty,
            _ => throw new InvalidOperationException("unknown actual tree admission outcome"),
        };
        var blocking = diagnostics
            .Where(static diagnostic =>
                diagnostic.AdmissionEffect is AdmissionEffect.Block or AdmissionEffect.HumanGate)
            .Select(static diagnostic => diagnostic.RuleId.Value)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var sl022 = diagnostics
            .Where(static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(22))
            .OrderBy(static diagnostic => diagnostic.Path, StringComparer.Ordinal)
            .ThenBy(static diagnostic => diagnostic.Message, StringComparer.Ordinal)
            .Select(static diagnostic => new ConservativeDiagnostic(
                diagnostic.RuleId.Value,
                diagnostic.Path,
                diagnostic.Message))
            .ToImmutableArray();
        var disposition = outcome is AdmissionOutcome.Admitted
            or AdmissionOutcome.ProtectedSurfaceChange
            ? ConservativeDisposition.Admit
            : ConservativeDisposition.Block;
        return new ConservativeCaseResult(
            caseId,
            caseRoot,
            disposition,
            blocking,
            sl022);
    }

    private static string BaseTreeCaseRoot(ConservativeHarnessInvocation invocation) =>
        CaseRoot(new
        {
            baseline_report_root = GoldenCorpusMaterializer.ContentRoot(
                invocation.Replay.BaselineLeanReport.AsSpan()),
            baseline_tree_oid = invocation.BaselineIdentity.TreeOid,
            candidate_report_root = GoldenCorpusMaterializer.ContentRoot(
                invocation.Replay.BaselineLeanReport.AsSpan()),
            candidate_tree_oid = invocation.BaselineIdentity.TreeOid,
            case_id = ConservativeExtensionCommand.BaseTreeCaseId,
            changes = Array.Empty<string>(),
        });

    private static string CandidateTreeCaseRoot(ConservativeHarnessInvocation invocation) =>
        CaseRoot(new
        {
            baseline_report_root = GoldenCorpusMaterializer.ContentRoot(
                invocation.Replay.BaselineLeanReport.AsSpan()),
            baseline_tree_oid = invocation.BaselineIdentity.TreeOid,
            candidate_report_root = GoldenCorpusMaterializer.ContentRoot(
                invocation.Replay.CandidateLeanReport.AsSpan()),
            candidate_tree_oid = invocation.CandidateIdentity.TreeOid,
            case_id = ConservativeExtensionCommand.CandidateTreeCaseId,
        });

    private static string CaseRoot<T>(T material)
    {
        var bytes = StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(material));
        return GoldenCorpusMaterializer.ContentRoot(bytes.AsSpan());
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

}
