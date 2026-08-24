using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CoverAtomCommand
{
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
