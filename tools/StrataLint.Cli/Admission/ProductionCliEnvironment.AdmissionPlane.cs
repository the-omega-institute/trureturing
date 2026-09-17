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
        DisplaySeverity.Error,
        "repository",
        AdmissionEffect.Block,
        RuleLifecycle.Active,
        null);

    internal static AdmissionOutcome? EvaluateAdmissionPlane(
        RawRepositorySnapshot candidate,
        RawRepositorySnapshot protectedBase,
        RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(changes);
        var decision = AdmissionPlanePolicy.Evaluate(
            candidate,
            protectedBase,
            changes);
        if (decision.IsAdmissible)
        {
            return null;
        }

        return decision.Classification is AdmissionPlaneClassification.Mixed
            ? new AdmissionOutcome.RuleRejected(ImmutableArray.Create(new Diagnostic(
                AdmissionPlaneRule.Id,
                AdmissionPlaneRule.Title,
                AdmissionPlaneRule.DisplaySeverity,
                AdmissionPlaneRule.AdmissionEffect,
                FileMapLoader.RelativePath,
                $"{decision.Code}: {decision.Message}")))
            : Failure(decision.Message);
    }

    private static AdmissionOutcome.InfrastructureFailure Failure(string message) => new(message);
}
