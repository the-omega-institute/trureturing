using System.Collections.Immutable;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal sealed partial class ProductionCliEnvironment
{
    // This gate runs before canonical FILEMAP validation so a malformed FILEMAP can repair
    // itself. Registering a post-canonical NoFindings stand-in would misstate enforcement.
    private static readonly RuleDescriptor AdmissionPlaneRule = new(
        RuleId.CreateKnown(29),
        "Admission plane partition",
        DisplaySeverity.Error,
        "repository",
        AdmissionEffect.Block,
        RuleLifecycle.Active,
        null);

    internal static AdmissionOutcome? EvaluateAdmissionPlane(
        RawRepositorySnapshot protectedBase,
        RawChangeSet changes,
        out bool usedBootstrap)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(changes);
        usedBootstrap = false;
        var changedPaths = AdmissionPlaneChangedPaths(changes);
        var decision = AdmissionPlanePolicy.Evaluate(
            protectedBase,
            changedPaths.Select(static path => path.Value).ToImmutableArray());
        usedBootstrap = decision.Classification is AdmissionPlaneClassification.Bootstrap;
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

    private static RawRepositorySnapshot WithoutFileMap(RawRepositorySnapshot snapshot) =>
        RawRepositorySnapshot.Create(snapshot.Entries.Where(
            static entry => entry.Path != FileMapLoader.RelativePath));
}
