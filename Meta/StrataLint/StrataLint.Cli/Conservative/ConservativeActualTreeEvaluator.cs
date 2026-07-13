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
        var lean = ValidateLean(snapshot, report);
        if (!snapshot.TryGetFile("Meta/registry.yaml", out var registryFile)
            || !snapshot.TryGetFile("Meta/domains.yaml", out var domainsFile))
        {
            throw new InvalidOperationException("baseline actual tree lacks policy files");
        }

        var registry = RegistryLoader.Load(
            registryFile.RawBytes.AsSpan(),
            domainsFile.RawBytes.AsSpan()) switch
        {
            RegistryLoadOutcome.Accepted accepted => accepted,
            RegistryLoadOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
        var dag = AcyclicTruthDag.Build(snapshot, lean) switch
        {
            DagBuildOutcome.Accepted accepted => accepted.Capability,
            DagBuildOutcome.Rejected rejected => throw new InvalidOperationException(
                "baseline actual tree truth DAG is cyclic: "
                + string.Join(" -> ", rejected.Witness.Select(static path => path.Value))),
        };
        var verifiedScribe = new ProductionScribeEmissionVerifier(invocation.BaselineRoot).Verify(report);
        var changes = RawChangeSet.Create(Array.Empty<string>());
        var bootstrap = BootstrapGate.Evaluate(changes) switch
        {
            BootstrapOutcome.Clear clear => clear.Capability,
            _ => throw new InvalidOperationException("empty baseline change set unexpectedly triggered SL-022"),
        };
        var admission = AdmissionPipeline.EvaluateWithScribe(
            snapshot,
            snapshot,
            registry.Policy,
            lean,
            lean,
            changes,
            bootstrap,
            verifiedScribe);
        if (admission is AdmissionOutcome.Admitted)
        {
            admission = ProductionFrozenLedgerValidator.Validate(
                    snapshot,
                    snapshot,
                    lean,
                    lean,
                    dag,
                    dag,
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
        ]);
        return Result(
            ConservativeExtensionCommand.CandidateTreeCaseId,
            CandidateTreeCaseRoot(invocation),
            admission);
    }

    private static ConservativeCaseResult Result(
        string caseId,
        string caseRoot,
        AdmissionOutcome outcome)
    {
        var diagnostics = outcome switch
        {
            AdmissionOutcome.RuleRejected rejected => rejected.Diagnostics,
            AdmissionOutcome.HumanReviewRequired required => required.Diagnostics,
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
            baseline_report_root = FileRoot(invocation.BaselineLeanReport),
            baseline_tree_oid = invocation.BaselineIdentity.TreeOid,
            candidate_report_root = FileRoot(invocation.BaselineLeanReport),
            candidate_tree_oid = invocation.BaselineIdentity.TreeOid,
            case_id = ConservativeExtensionCommand.BaseTreeCaseId,
            changes = Array.Empty<string>(),
        });

    private static string CandidateTreeCaseRoot(ConservativeHarnessInvocation invocation) =>
        CaseRoot(new
        {
            baseline_report_root = FileRoot(invocation.BaselineLeanReport),
            baseline_tree_oid = invocation.BaselineIdentity.TreeOid,
            candidate_report_root = FileRoot(invocation.CandidateLeanReport),
            candidate_tree_oid = invocation.CandidateIdentity.TreeOid,
            case_id = ConservativeExtensionCommand.CandidateTreeCaseId,
        });

    private static string CaseRoot<T>(T material)
    {
        var bytes = StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(material));
        return GoldenCorpusMaterializer.ContentRoot(bytes.AsSpan());
    }

    private static string FileRoot(string path) =>
        GoldenCorpusMaterializer.ContentRoot(File.ReadAllBytes(path));

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
}
