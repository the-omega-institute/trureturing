using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DigestionReceiptIntegrityGuard
{
    internal static void RequireNoFailures(
        DigestionLedgerEvaluation evaluation,
        ImmutableHashSet<DigestionReceiptIntegrityGapIdentity>? allowed = null)
    {
        var failures = DigestionReceiptIntegrity.Identities(evaluation)
            .Where(identity => allowed?.Contains(identity) != true)
            .Select(DigestionReceiptIntegrity.Render)
            .ToArray();
        ThrowIfAny(failures);
    }

    internal static void RequireNoNewFailures(
        DigestionLedgerEvaluation before,
        DigestionLedgerEvaluation candidate) =>
        ThrowIfAny(DigestionReceiptIntegrity.NewFailureReasons(before, candidate));

    internal static void RequireExactScribeRepairComplete(
        DigestionLedgerEvaluation evaluation,
        string atomId,
        string gid) =>
        ThrowIfAny(DigestionReceiptIntegrity.ExactScribeRepairIdentities(evaluation, atomId, gid)
            .Select(DigestionReceiptIntegrity.Render));

    internal static RawChangeSet IncludePlannedPaths(
        RawChangeSet changes,
        IEnumerable<string> paths) =>
        RawChangeSet.Create(changes.Paths
            .Select(static path => path.Value)
            .Concat(paths)
            .Distinct(StringComparer.Ordinal));

    private static void ThrowIfAny(IEnumerable<string> reasons)
    {
        var materialized = reasons.ToArray();
        if (materialized.Length > 0)
        {
            throw new InvalidOperationException(
                "receipt integrity evaluation failed: " + string.Join("; ", materialized));
        }
    }
}
