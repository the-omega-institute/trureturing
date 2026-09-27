using System.Collections.Immutable;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal sealed partial class ProductionCliEnvironment
{
    // Current paths use candidate FILEMAP; snapshot-confirmed deletions use protected-base FILEMAP.
    // Required manifests must be available and valid before canonical validation.
    private static readonly RuleDescriptor AdmissionPlaneRule = new(
        RuleId.CreateKnown(29),
        "Admission plane partition",
        DisplaySeverity.Warning,
        "repository",
        AdmissionEffect.Observe,
        RuleLifecycle.Active,
        null);

    internal static AdmissionOutcome.InfrastructureFailure? EvaluateAdmissionPlane(
        RawRepositorySnapshot candidate,
        RawRepositorySnapshot protectedBase,
        RawChangeSet changes,
        out ImmutableArray<Diagnostic> observations)
    {
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(changes);
        var decision = AdmissionPlanePolicy.Evaluate(
            candidate,
            protectedBase,
            changes);
        observations = decision.Classification is AdmissionPlaneClassification.Mixed
            ? [new Diagnostic(
                AdmissionPlaneRule.Id,
                AdmissionPlaneRule.Title,
                AdmissionPlaneRule.DisplaySeverity,
                AdmissionPlaneRule.AdmissionEffect,
                FileMapLoader.RelativePath,
                $"{decision.Code}: {decision.Message}")]
            : [];
        return decision.IsAdmissible ? null : Failure(decision.Message);
    }

    // SL-029 is evaluated before the rule catalog. Preserve its actual finding
    // without changing the core outcome, certificate, or rule execution evidence.
    private static AdmissionOutcome WithAdmissionPlaneObservations(
        AdmissionOutcome outcome, ImmutableArray<Diagnostic> observations) => observations.IsEmpty ? outcome : outcome switch
    {
        AdmissionOutcome.Admitted admitted => new AdmissionOutcome.Admitted(
            admitted.Certificate, admitted.Observations.AddRange(observations)),
        AdmissionOutcome.ProtectedSurfaceChange change => new AdmissionOutcome.ProtectedSurfaceChange(
            change.ContentCertificate, change.ChangeSet, change.Sl022Diagnostics, change.Observations.AddRange(observations)),
        AdmissionOutcome.RuleRejected rejected => new AdmissionOutcome.RuleRejected(rejected.Diagnostics.AddRange(observations)),
        AdmissionOutcome.InfrastructureFailure failure => failure with { Observations = failure.Observations.AddRange(observations) },
        AdmissionOutcome.ProtectedSurfaceVerificationRequired verification =>
            new AdmissionOutcome.ProtectedSurfaceVerificationRequired(verification.Diagnostics.AddRange(observations)),
    };

    private static AdmissionOutcome.InfrastructureFailure Failure(string message) => new(message);
}
