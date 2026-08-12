using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CoverAtomCommand
{
    private static ImmutableArray<DigestionLedgerEntry> FindCrossAtomBindings(
        ImmutableArray<DigestionLedgerSource> sources,
        string atomId,
        string gid) =>
        sources
            .SelectMany(static source => source.Entries)
            .Where(entry => !string.Equals(entry.AtomId, atomId, StringComparison.Ordinal))
            .Where(entry => entry.CoverageGids.Contains(gid, StringComparer.Ordinal))
            .ToImmutableArray();

    private static void RequireSharedResidualHost(
        DigestionLedgerEntry target,
        DigestionLedgerEntry conflict,
        BackfillInventoryDocument baselineDocument,
        RepositorySnapshot baseline,
        LeanAxiomReport report,
        string gid)
    {
        if (target.CoverageGids.Length == 0
            || !string.Equals(target.AstPath, conflict.AstPath, StringComparison.Ordinal))
        {
            throw CrossAtomBinding(gid, conflict.AtomId);
        }

        var baselineTarget = LocateEntry(
            baselineDocument.RequireDigestionSources(),
            target.AtomId,
            "baseline shared-residual target");
        var baselineConflict = LocateEntry(
            baselineDocument.RequireDigestionSources(),
            conflict.AtomId,
            "baseline shared-residual host");
        if (!string.Equals(baselineTarget.AstPath, baselineConflict.AstPath, StringComparison.Ordinal)
            || !string.Equals(target.AstPath, baselineTarget.AstPath, StringComparison.Ordinal)
            || !string.Equals(conflict.AstPath, baselineConflict.AstPath, StringComparison.Ordinal)
            || conflict.Fingerprints != baselineConflict.Fingerprints
            || !string.Equals(conflict.CasRef, baselineConflict.CasRef, StringComparison.Ordinal))
        {
            throw CrossAtomBinding(gid, conflict.AtomId);
        }

        DigestionFormalizationReceiptVerifier.RequireAuthorizedCoverage(
            baseline,
            DigestionFormalizationReceipt.PathFor(conflict.AtomId),
            conflict,
            baselineConflict.CoverageGids,
            conflict.CoverageGids.Where(candidate =>
                !baselineConflict.CoverageGids.Contains(candidate, StringComparer.Ordinal)),
            report);
    }

    private static DigestionLedgerEntry LocateEntry(
        ImmutableArray<DigestionLedgerSource> sources,
        string atomId,
        string context)
    {
        var matches = sources
            .SelectMany(static source => source.Entries)
            .Where(entry => string.Equals(entry.AtomId, atomId, StringComparison.Ordinal))
            .ToArray();
        if (matches.Length != 1)
        {
            throw new InvalidOperationException(
                $"{context} atom {atomId} must occur exactly once");
        }

        return matches[0];
    }

    private static InvalidOperationException CrossAtomBinding(string gid, string atomId) =>
        new($"cover GID {gid} is already bound to atom {atomId}");

    private static void RequireHostedExtension(
        DigestionEntryEvaluation before,
        DigestionEntryEvaluation after,
        ImmutableArray<string> addedGids,
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean)
    {
        var dag = AcyclicTruthDag.Build(snapshot, lean) switch
        {
            DagBuildOutcome.Accepted accepted => accepted.Capability,
            DagBuildOutcome.Rejected rejected => throw new InvalidOperationException(
                "hosted cover truth DAG is cyclic: "
                + string.Join(" -> ", rejected.Witness.Select(static path => path.Value))),
        };
        var nodes = dag.Nodes.ToDictionary(static node => node.RepoPath);
        foreach (var gidText in addedGids)
        {
            if (!Gid.TryParse(gidText, out var gid)
                || !nodes.TryGetValue(gid.Path, out var node)
                || node.State != TruthState.Closed)
            {
                throw new InvalidOperationException(
                    $"hosted cover GID {gidText} must belong to a Closed Lean module");
            }
        }

        var added = addedGids.ToImmutableHashSet(StringComparer.Ordinal);
        var addedGaps = after.Gaps
            .Where(gap => added.Contains(gap.Detail))
            .ToArray();
        if (addedGaps.Length > 0)
        {
            throw new InvalidOperationException(
                $"hosted cover atom {after.Entry.AtomId} has gaps for newly added GIDs: "
                + string.Join(",", addedGaps.Select(static gap => gap.Code)));
        }

        var beforeGaps = before.Gaps
            .Select(static gap => (gap.Code, gap.Detail))
            .ToHashSet();
        var regressions = after.Gaps
            .Where(gap => !beforeGaps.Contains((gap.Code, gap.Detail)))
            .ToArray();
        if (after.DerivedStatus.Migration < before.DerivedStatus.Migration
            || TruthRank(after.DerivedStatus.Truth) < TruthRank(before.DerivedStatus.Truth)
            || regressions.Length > 0)
        {
            throw new InvalidOperationException(
                $"hosted cover atom {after.Entry.AtomId} regressed from {before.Render()} "
                + $"to {after.Render()}");
        }
    }

    private static int TruthRank(DigestionTruthState truth) => truth switch
    {
        DigestionTruthState.Open => 0,
        DigestionTruthState.Tail => 1,
        DigestionTruthState.Closed => 2,
        _ => throw new ArgumentOutOfRangeException(nameof(truth)),
    };
}
