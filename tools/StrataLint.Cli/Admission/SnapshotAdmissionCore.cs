using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record SnapshotAdmissionEvaluation(
    AdmissionOutcome Outcome,
    AcceptedLeanClosure? CurrentLean);

internal static class SnapshotAdmissionCore
{
    internal static SnapshotAdmissionEvaluation Evaluate(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        LeanAxiomReport currentReport,
        RawChangeSet changes,
        BootstrapOutcome bootstrap,
        VerifiedScribeEmissions? verifiedScribeEmissions,
        RepositorySnapshot? forkPoint = null,
        AdmissionCheckTiming? timing = null)
    {
        var phaseTiming = timing ?? AdmissionCheckTiming.Disabled;
        try
        {
            if (bootstrap is BootstrapOutcome.InfrastructureFailure bootstrapFailure)
            {
                return Failure(bootstrapFailure.Message);
            }

            var sl022Diagnostics = bootstrap is
                BootstrapOutcome.ProtectedSurfaceVerificationRequired bootstrapVerification
                ? BootstrapGate.CreateSl022Diagnostics(bootstrapVerification.ChangeSet)
                : ImmutableArray<Diagnostic>.Empty;
            var registry = phaseTiming.Measure(
                "policy-load",
                () =>
                {
                    if (!current.TryGetFile("Meta/registry.yaml", out var registryFile)
                        || !current.TryGetFile("Meta/domains.yaml", out var domainsFile))
                    {
                        throw new InvalidOperationException(
                            "current snapshot lacks Meta/registry.yaml or Meta/domains.yaml");
                    }

                    return RegistryLoader.Load(
                        registryFile.RawBytes.AsSpan(),
                        domainsFile.RawBytes.AsSpan()) switch
                    {
                        RegistryLoadOutcome.Accepted accepted => accepted,
                        RegistryLoadOutcome.InfrastructureFailure failure =>
                            throw new InvalidOperationException(failure.Message),
                    };
                });
            var lean = phaseTiming.Measure(
                "lean-closure",
                () => ValidateLean(current, currentReport));

            var admission = phaseTiming.Measure(
                "rule-passes",
                () => bootstrap switch
                {
                    BootstrapOutcome.Clear clear => AdmissionPipeline.EvaluateWithScribe(
                        current,
                        baseline,
                        registry.Policy,
                        lean,
                        changes,
                        clear.Capability,
                        verifiedScribeEmissions,
                        forkPoint,
                        MeasureRule),
                    BootstrapOutcome.ProtectedSurfaceVerificationRequired protectedSurfaceVerification =>
                        AdmissionPipeline.EvaluateProtectedSurface(
                            current,
                            baseline,
                            registry.Policy,
                            lean,
                            changes,
                            protectedSurfaceVerification.ChangeSet,
                            verifiedScribeEmissions,
                            forkPoint,
                            MeasureRule),
                    _ => throw new InvalidOperationException("unknown bootstrap outcome"),
                },
                static outcome => outcome is not AdmissionOutcome.Admitted
                    && outcome is not AdmissionOutcome.ProtectedSurfaceChange);
            if (admission is not AdmissionOutcome.Admitted
                && admission is not AdmissionOutcome.ProtectedSurfaceChange)
            {
                admission = PreserveSl022Diagnostics(admission, sl022Diagnostics);
            }

            return new SnapshotAdmissionEvaluation(
                admission,
                lean);

            ImmutableArray<RuleFinding> MeasureRule(
                RuleId ruleId,
                AdmissionEffect admissionEffect,
                Func<ImmutableArray<RuleFinding>> evaluate) =>
                phaseTiming.Measure(
                    "rule-" + ruleId.Value.ToLowerInvariant(),
                    evaluate,
                    findings => findings.Any(finding =>
                        (finding.Effect ?? admissionEffect) is AdmissionEffect.Block));
        }
        catch (Exception exception)
        {
            return Failure(exception.Message);
        }
    }

    private static SnapshotAdmissionEvaluation Failure(string message) => new(
        new AdmissionOutcome.InfrastructureFailure(message),
        null);

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    internal static AdmissionOutcome PreserveSl022Diagnostics(
        AdmissionOutcome outcome,
        ImmutableArray<Diagnostic> expected)
    {
        if (expected.IsDefaultOrEmpty || outcome is not AdmissionOutcome.RuleRejected rejected)
        {
            return outcome;
        }

        var actual = rejected.Diagnostics
            .Where(static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(22))
            .OrderBy(static diagnostic => diagnostic.Path, StringComparer.Ordinal)
            .ToImmutableArray();
        if (actual.IsEmpty)
        {
            return new AdmissionOutcome.RuleRejected(rejected.Diagnostics.AddRange(expected));
        }

        return actual.SequenceEqual(expected)
            ? outcome
            : new AdmissionOutcome.InfrastructureFailure(
                "SL-022 rejection evidence disagrees with the bootstrap meta change set");
    }
}
