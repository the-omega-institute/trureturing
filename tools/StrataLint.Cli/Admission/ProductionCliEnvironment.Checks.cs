using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal sealed partial class ProductionCliEnvironment
{
    public ExplicitCommandResult CheckCurrent(IReadOnlyList<string> arguments) => CheckStage(arguments, delta: false);

    public ExplicitCommandResult CheckDelta(IReadOnlyList<string> arguments) => CheckStage(arguments, delta: true);

    private ExplicitCommandResult CheckStage(IReadOnlyList<string> arguments, bool delta)
    {
        var timing = new AdmissionCheckTiming(timeProvider);
        ImmutableArray<Diagnostic> planeObservations = [];
        try
        {
            var options = ParseCheckArguments(arguments);
            if (options.CandidateLeanReport is null || (!delta && options.ProtectedBase is not null)
                || (delta && options.ProtectedBase is null))
                throw new InvalidOperationException(delta
                    ? "check-delta requires --protected-base and --candidate-lean-report"
                    : "check-current requires --candidate-lean-report and accepts no base");

            var raw = timing.Measure("repository-read", () => repository.ReadCurrent());
            var prepared = delta ? timing.Measure("repository-prepare", () => repository.Prepare(options.ProtectedBase)) : null;
            var baselineRaw = prepared is null ? null : timing.Measure("repository-read-base", () => repository.ReadRevision(prepared.Revision));
            var observedPlane = ImmutableArray<Diagnostic>.Empty;
            var planeFailure = prepared is null ? null
                : timing.Measure("admission-plane", () => EvaluateAdmissionPlane(raw, baselineRaw!, prepared.Changes, out observedPlane));
            planeObservations = observedPlane;
            if (planeFailure is not null)
                return new(2, RenderPlaneObservations(planeObservations), planeFailure.Message + "\n");

            var current = timing.Measure("snapshot-load", () => Decode(raw));
            var report = timing.Measure("lean-report-load", () => RawLeanReportArtifact.ReadFile(options.CandidateLeanReport!, current, validateMaterials: true));
            var policy = timing.Measure("policy-load", () => RepositoryPolicyLoader.Load(current) switch
            {
                PolicyLoadOutcome.Accepted accepted => accepted.Policy,
                PolicyLoadOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
            });
            var lean = timing.Measure("lean-closure", () => LeanClosureValidator.Validate(current, report) switch
            {
                LeanValidationOutcome.Accepted accepted => accepted.Capability,
                LeanValidationOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
            });

            RuleExecutionOutcome result;
            if (prepared is not null)
            {
                var baseline = timing.Measure("snapshot-load-base", () => Decode(baselineRaw!));
                var topology = timing.Measure("test-topology", () => RepositoryRules.EvaluateSnapshots(baseline, current), static outcome => !outcome.IsAccepted);
                if (!topology.IsAccepted)
                    return new(1, RenderPlaneObservations(planeObservations) + "TEST_PROJECT_TOPOLOGY " + topology.Message + "\n", "");
                var meta = BootstrapGate.Evaluate(prepared.Changes) switch
                {
                    BootstrapOutcome.Clear clear => MetaEvaluationProfile.ForClear(clear.Capability),
                    BootstrapOutcome.ProtectedSurfaceVerificationRequired change => MetaEvaluationProfile.ForProtectedSurface(change.ChangeSet),
                    BootstrapOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
                };
                result = timing.Measure("rule-passes", () => AdmissionPipeline.CheckDelta(
                    DeltaRuleContext.Create(current, baseline, policy, lean, prepared.Changes, meta, null), MeasureRule), Blocked);
            }
            else
            {
                var verified = timing.Measure("scribe-verify", () => VerifyScribeForAdmission(scribeEmissionVerifier, current, report));
                result = timing.Measure("rule-passes", () => AdmissionPipeline.CheckCurrent(
                    CurrentRuleContext.Create(current, policy, lean, verified), MeasureRule), Blocked);
                if (timing.Measure("canonicalization", () => RepositoryCanonicalizer.Validate(current, policy),
                        static outcome => outcome is CanonicalizationOutcome.InfrastructureFailure) is CanonicalizationOutcome.InfrastructureFailure failure)
                    return new(2, RenderStage(result, planeObservations).Output, "INFRASTRUCTURE_FAILURE " + failure.Message + "\n");
            }
            return RenderStage(result, planeObservations);
        }
        catch (Exception exception)
        {
            return new(2, RenderPlaneObservations(planeObservations), "INFRASTRUCTURE_FAILURE " + exception.Message + "\n");
        }

        ImmutableArray<RuleFinding> MeasureRule(RuleId ruleId, AdmissionEffect admissionEffect, Func<ImmutableArray<RuleFinding>> evaluate) =>
            timing.Measure("rule-" + ruleId.Value.ToLowerInvariant(), evaluate,
                findings => findings.Any(finding => (finding.Effect ?? admissionEffect) is AdmissionEffect.Block));
    }

    private static string RenderPlaneObservations(ImmutableArray<Diagnostic> observations) =>
        observations.IsDefaultOrEmpty ? "" : JsonSerializer.Serialize(new { diagnostics = observations }) + "\n";

    private static ExplicitCommandResult RenderStage(RuleExecutionOutcome result,
        ImmutableArray<Diagnostic> planeObservations = default)
    {
        if (result is RuleExecutionOutcome.InfrastructureFailure failure)
            return new(2, RenderPlaneObservations(planeObservations), failure.Message + "\n");
        var rules = ((RuleExecutionOutcome.Completed)result).Capability;
        var blocked = rules.Diagnostics.Any(d => d.AdmissionEffect is AdmissionEffect.Block
            || d.AdmissionEffect is AdmissionEffect.HumanGate && d.RuleId != RuleId.CreateKnown(22));
        var annotated = rules.Diagnostics.Any(d => d.RuleId == RuleId.CreateKnown(22) && d.AdmissionEffect is AdmissionEffect.HumanGate);
        return new(blocked ? 1 : annotated ? 3 : 0, JsonSerializer.Serialize(new
        {
            executed = rules.ExecutedRules.Select(id => id.Value),
            skipped = rules.SkippedRules.Select(id => id.Value),
            deferred = rules.DeferredRules,
            diagnostics = planeObservations.IsDefaultOrEmpty ? rules.Diagnostics : rules.Diagnostics.AddRange(planeObservations),
        }) + "\n", "");
    }

    private static bool Blocked(RuleExecutionOutcome outcome) =>
        outcome is not RuleExecutionOutcome.Completed completed
        || completed.Capability.Diagnostics.Any(diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Block);
}
