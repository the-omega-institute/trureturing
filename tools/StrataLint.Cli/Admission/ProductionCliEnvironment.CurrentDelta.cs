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
        try
        {
            var options = ParseCheckArguments(arguments);
            if (options.CandidateLeanReport is null || (!delta && options.ProtectedBase is not null))
                throw new InvalidOperationException("check-current requires a candidate report and accepts no base; check-delta requires an explicit base and report");
            var raw = repository.ReadCurrent();
            var current = Decode(raw);
            var report = RawLeanReportArtifact.ReadFile(options.CandidateLeanReport, current, validateMaterials: true);
            if (!current.TryGetFile("Meta/registry.yaml", out var registry) || !current.TryGetFile("Meta/domains.yaml", out var domains))
                throw new InvalidDataException("candidate policy is missing");
            var policy = RegistryLoader.Load(registry.RawBytes.AsSpan(), domains.RawBytes.AsSpan()) switch
            {
                RegistryLoadOutcome.Accepted accepted => accepted.Policy,
                RegistryLoadOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
            };
            var lean = LeanClosureValidator.Validate(current, report) switch
            {
                LeanValidationOutcome.Accepted accepted => accepted.Capability,
                LeanValidationOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
            };
            RuleExecutionOutcome result;
            if (delta)
            {
                var prepared = repository.Prepare(options.ProtectedBase);
                var baseline = Decode(repository.ReadRevision(prepared.Revision));
                var baseProjects = EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(baseline));
                removedProjectOutput = string.Concat(baseProjects.Where(path => !current.TryGetFile(path, out _))
                    .Select(path => $"ENGINEERING_TEST_PROJECT_REMOVED project={JsonSerializer.Serialize(path)}\n"));
                var common = CommonExecutionEvidence.ValidateCommon(repositoryRoot, baseProjects);
                if (!string.Equals(Path.GetFullPath(options.CandidateLeanReport), Path.Combine(repositoryRoot, CommonExecutionEvidence.ReportPath), StringComparison.Ordinal))
                    throw new InvalidDataException("check-delta requires this round's canonical report");
                if (EvaluateAdmissionPlane(raw, prepared.Changes) is { } plane)
                    return StageAdmissionFailure(plane);
                var topology = RepositoryRules.EvaluateSnapshots(baseline, current);
                if (!topology.IsAccepted) return new(1, "TEST_PROJECT_TOPOLOGY " + topology.Message + "\n", "");
                var meta = BootstrapGate.Evaluate(prepared.Changes) switch
                {
                    BootstrapOutcome.Clear clear => MetaEvaluationProfile.ForClear(clear.Capability),
                    BootstrapOutcome.ProtectedSurfaceVerificationRequired change => MetaEvaluationProfile.ForProtectedSurface(change.ChangeSet),
                    BootstrapOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
                };
                var metadata = CommonCompileMetadata.Load(repositoryRoot, common.Build.Materials);
                ScribeTestMap Derive(RepositorySnapshot snapshot) => ScribeTestMapDeriver.DeriveSnapshot(snapshot, metadata);
                var cacheRoot = options.TestMapCacheRoot ?? Environment.GetEnvironmentVariable("STRATALINT_TEST_MAP_CACHE_ROOT");
                var testMapStore = cacheRoot is null ? null : TryCreateTestMapStore(cacheRoot, out _, Derive, metadata);
                result = AdmissionPipeline.CheckDelta(DeltaRuleContext.Create(current, baseline, policy, lean, prepared.Changes, meta, null,
                    testMapStore: testMapStore, deriveTestMap: Derive,
                    commonResults: new CandidateCommonResults(common.Current.Candidate, common.Current.Round)));
            }
            else
            {
                var verified = VerifyScribeForAdmission(scribeEmissionVerifier, current, report);
                result = AdmissionPipeline.CheckCurrent(CurrentRuleContext.Create(current, policy, lean, verified));
                if (RepositoryCanonicalizer.Validate(current, policy) is CanonicalizationOutcome.InfrastructureFailure failure)
                    return new(2, RenderStage(result).Output, "INFRASTRUCTURE_FAILURE " + failure.Message + "\n");
            }
            return RenderStage(result);
        }
        catch (Exception exception)
        {
            return new(2, removedProjectOutput, "INFRASTRUCTURE_FAILURE " + exception.Message + "\n");
        }
    }

    private static ExplicitCommandResult StageAdmissionFailure(AdmissionOutcome outcome) => outcome switch
    {
        AdmissionOutcome.RuleRejected rejected => new(1, JsonSerializer.Serialize(rejected.Diagnostics) + "\n", ""),
        AdmissionOutcome.InfrastructureFailure failure => new(2, "", failure.Message + "\n"),
        _ => new(2, "", "unexpected admission plane outcome\n"),
    };

    private static ExplicitCommandResult RenderStage(RuleExecutionOutcome result)
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
        }) + "\n", "");
    }
}
