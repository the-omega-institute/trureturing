using System.Collections.Immutable;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal sealed partial class ProductionCliEnvironment
{
    // This gate classifies changed paths from the candidate FILEMAP before canonical validation.
    // It fails closed when FILEMAP is missing or invalid, so a correcting PR carries a valid manifest.
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
        RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(changes);
        var changedPaths = AdmissionPlaneChangedPaths(changes);
        var decision = AdmissionPlanePolicy.Evaluate(
            candidate,
            changedPaths.Select(static path => path.Value).ToImmutableArray());
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

    private static ImmutableArray<RepoPath> AdmissionPlaneChangedPaths(RawChangeSet changes) =>
        changes.Entries
            .Where(static change => change.Kind switch
            {
                RawChangeKind.Added => true,
                RawChangeKind.Modified => true,
                RawChangeKind.Deleted => true,
                RawChangeKind.Copied => false,
                _ => throw new InvalidOperationException(
                    $"unsupported raw change kind: {change.Kind}"),
            })
            .Select(static change => change.Path)
            .ToImmutableArray();

    private static AdmissionOutcome.InfrastructureFailure Failure(string message) => new(message);
}
