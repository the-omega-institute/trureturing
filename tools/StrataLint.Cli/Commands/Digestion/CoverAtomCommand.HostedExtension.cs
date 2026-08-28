using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CoverAtomCommand
{
    private static void RequireHostedExtension(
        DigestionEntryEvaluation before,
        DigestionEntryEvaluation after,
        ImmutableArray<string> addedGids,
        IReadOnlyDictionary<RepoPath, TruthState> truthStates)
    {
        foreach (var gidText in addedGids)
        {
            if (!Gid.TryParse(gidText, out var gid)
                || !truthStates.TryGetValue(gid.Path, out var state)
                || state != TruthState.Closed)
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
