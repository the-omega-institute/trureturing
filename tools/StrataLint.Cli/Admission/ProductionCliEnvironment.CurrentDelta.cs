using System.Text.Json;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal sealed partial class ProductionCliEnvironment
{
    public ExplicitCommandResult CheckCurrent(IReadOnlyList<string> arguments) => CheckStage(arguments, delta: false);

    public ExplicitCommandResult CheckDelta(IReadOnlyList<string> arguments) => CheckStage(arguments, delta: true);

    private ExplicitCommandResult CheckStage(IReadOnlyList<string> arguments, bool delta)
    {
        var removedProjectOutput = string.Empty;
        TestProjectExecution[] acceptedBaseTests = [];
        try
        {
            string? commonRound = null, commonPlan = null, commonChanges = null;
            while (!delta && arguments.Count >= 2 && arguments[^2].StartsWith("--common-", StringComparison.Ordinal))
            {
                switch (arguments[^2])
                {
                    case "--common-build-round" when commonRound is null: commonRound = arguments[^1]; break;
                    case "--common-plan" when commonPlan is null: commonPlan = arguments[^1]; break;
                    case "--common-changes" when commonChanges is null: commonChanges = arguments[^1]; break;
                    default: throw new InvalidDataException("invalid common current option");
                }
                arguments = arguments.Take(arguments.Count - 2).ToArray();
            }
            var resourcePlan = ResourceExecutionPlan.Load(repositoryRoot, commonPlan, commonChanges);
            if (resourcePlan is not null && commonRound is null) throw new InvalidDataException("selected current requires a common build round");
            var options = ParseCheckArguments(arguments);
            var reportRequired = delta || commonRound is null || resourcePlan is null || resourcePlan.CurrentSteps.Contains("lean-report");
            if (reportRequired && options.CandidateLeanReport is null || !delta && options.ProtectedBase is not null)
                throw new InvalidOperationException("check-current requires a candidate report and accepts no base; check-delta requires an explicit base and report");
            if (!reportRequired && options.CandidateLeanReport is not null)
                throw new InvalidDataException("unrequested report cannot be current evidence");
            var raw = repository.ReadCurrent();
            var current = Decode(raw);
            var validation = new CommonExecutionEvidence.ValidationScope(current);
            var manifest = validation.CheckManifest();
            var selectedIds = resourcePlan?.CheckUnits.Except(CommonExecutionEvidence.EngineeringCheckIds).Order(StringComparer.Ordinal).ToArray();
            if (!reportRequired && manifest.Any(check => selectedIds!.Contains(check.Id) && check.ReportInputs.Length != 0))
                throw new InvalidDataException("selected current checks require Lean report evidence");
            var report = !reportRequired ? null : !delta && commonRound is null
                ? RawLeanReportArtifact.ReadFile(options.CandidateLeanReport!, current, validateMaterials: true)
                : validation.Report(options.CandidateLeanReport!);
            if (!current.TryGetFile("Meta/registry.yaml", out var registry) || !current.TryGetFile("Meta/domains.yaml", out var domains))
                throw new InvalidDataException("candidate policy is missing");
            var policy = RegistryLoader.Load(registry.RawBytes.AsSpan(), domains.RawBytes.AsSpan()) switch
            {
                RegistryLoadOutcome.Accepted accepted => accepted.Policy,
                RegistryLoadOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
            };
            var lean = report is null ? null : LeanClosureValidator.Validate(current, report) switch
            {
                LeanValidationOutcome.Accepted accepted => accepted.Capability,
                LeanValidationOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
            };
            RuleExecutionOutcome result;
            if (delta)
            {
                var prepared = repository.Prepare(options.ProtectedBase);
                var baselineRaw = repository.ReadRevision(prepared.Revision);
                var baseline = Decode(baselineRaw);
                var baseProjects = EngineeringProjectRegistry.ReadBase(baseline, current)
                    .Where(project => project.Ci).Select(project => project.Path).Order(StringComparer.Ordinal).ToArray();
                removedProjectOutput = string.Concat(baseProjects.Where(path => !current.TryGetFile(path, out _))
                    .Select(path => $"ENGINEERING_TEST_PROJECT_REMOVED project={JsonSerializer.Serialize(path)}\n"));
                var common = CommonExecutionEvidence.ValidateCommon(repositoryRoot, validation, baseProjects);
                acceptedBaseTests = common.Tests.Projects
                    .Where(row => baseProjects.Contains(row.Project, StringComparer.Ordinal)).ToArray();
                if (!string.Equals(Path.GetFullPath(options.CandidateLeanReport!), Path.Combine(repositoryRoot, CommonExecutionEvidence.ReportPath), StringComparison.Ordinal))
                    throw new InvalidDataException("check-delta requires this round's canonical report");
                if (EvaluateAdmissionPlane(raw, baselineRaw, prepared.Changes) is { } plane)
                    return StageAdmissionFailure(plane);
                var topology = RepositoryRules.EvaluateSnapshots(baseline, current);
                if (!topology.IsAccepted) return new(1, "TEST_PROJECT_TOPOLOGY " + topology.Message + "\n", "");
                var meta = BootstrapGate.Evaluate(prepared.Changes) switch
                {
                    BootstrapOutcome.Clear clear => MetaEvaluationProfile.ForClear(clear.Capability),
                    BootstrapOutcome.ProtectedSurfaceVerificationRequired change => MetaEvaluationProfile.ForProtectedSurface(change.ChangeSet),
                    BootstrapOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
                };
                BindInformationTemplateHistory(report!, current, prepared.Revision, options.CandidateLeanReport!);
                result = AdmissionPipeline.CheckDelta(DeltaRuleContext.Create(current, baseline, policy, lean!, prepared.Changes, meta, null,
                    commonResults: new CandidateCommonResults(common.Current.Candidate, common.Current.Round)));
            }
            else
            {
                if (commonRound is not null)
                {
                    if (reportRequired && Path.GetFullPath(options.CandidateLeanReport!, repositoryRoot) != Path.Combine(repositoryRoot, CommonExecutionEvidence.ReportPath))
                        throw new InvalidDataException("common current requires canonical report material");
                    return ExecuteCommonCurrent(commonRound, validation, policy, lean, report, selectedIds);
                }
                var verified = VerifyScribeForAdmission(scribeEmissionVerifier, current, report!);
                result = AdmissionPipeline.CheckCurrent(CurrentRuleContext.Create(current, policy, lean!, verified));
                if (RepositoryCanonicalizer.Validate(current, policy) is CanonicalizationOutcome.InfrastructureFailure failure)
                    return new(2, RenderStage(result).Output, "INFRASTRUCTURE_FAILURE " + failure.Message + "\n");
            }
            return RenderStage(result, acceptedBaseTests);
        }
        catch (Exception exception)
        {
            return new(2, removedProjectOutput, "INFRASTRUCTURE_FAILURE " + exception.Message + "\n");
        }
    }

    private void BindInformationTemplateHistory(LeanAxiomReport report, RepositorySnapshot current,
        string protectedRevision, string candidateReportPath)
    {
        // Historical content is data for the current producer. The protected
        // revision and seed remain immutable inputs selected by the delta rule.
        report.TemplateEvidenceContext = new(protectedRevision, revision =>
        {
            InformationTemplateJson.Hash(revision, 40);
            var historical = Decode(repository.ReadRevision(revision));
            var path = Path.Combine(Path.GetDirectoryName(Path.GetFullPath(candidateReportPath))!,
                "information-template-history", revision, "raw-lean-report.json");
            return new(historical, RawLeanReportArtifact.ReadFile(path,
                InformationTemplateEvidence.HistoricalInputs(historical, current)));
        });
    }

    private static ExplicitCommandResult StageAdmissionFailure(AdmissionOutcome outcome) => outcome switch
    {
        AdmissionOutcome.RuleRejected rejected => new(1, JsonSerializer.Serialize(rejected.Diagnostics) + "\n", ""),
        AdmissionOutcome.InfrastructureFailure failure => new(2, "", failure.Message + "\n"),
        _ => new(2, "", "unexpected admission plane outcome\n"),
    };

    private static ExplicitCommandResult RenderStage(RuleExecutionOutcome result, TestProjectExecution[]? acceptedBaseTests = null)
    {
        if (result is RuleExecutionOutcome.InfrastructureFailure failure) return new(2, "", failure.Message + "\n");
        var rules = ((RuleExecutionOutcome.Completed)result).Capability;
        var blocked = rules.Diagnostics.Any(d => d.AdmissionEffect is AdmissionEffect.Block
            || d.AdmissionEffect is AdmissionEffect.HumanGate && d.RuleId != RuleId.CreateKnown(22));
        var annotated = rules.Diagnostics.Any(d => d.RuleId == RuleId.CreateKnown(22) && d.AdmissionEffect is AdmissionEffect.HumanGate);
        return new(blocked ? 1 : annotated ? 3 : 0, JsonSerializer.Serialize(new
        {
            executed = rules.ExecutedRules.Select(id => id.Value),
            skipped = rules.SkippedRules.Select(id => id.Value),
            deferred = rules.DeferredRules,
            diagnostics = rules.Diagnostics,
            accepted_base_tests = (acceptedBaseTests ?? []).Select(row => new { project = row.Project, status = row.Status,
                execution_candidate = row.ExecutionCandidate, execution_round = row.ExecutionRound }),
        }) + "\n", "");
    }
}
