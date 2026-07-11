using System.Collections.Immutable;
using Dunet;

namespace StrataLint.Engine;

[Union(EnableImplicitConversions = false)]
public partial record FrozenLedgerChangeOutcome
{
    public partial record NoLedgerChange;

    public partial record LedgerOnly;

    public partial record HarnessOnly;

    public partial record ForbiddenMixed(ImmutableArray<RepoPath> Paths);
}

public static class FrozenLedgerChangeClassifier
{
    public const string LedgerPath = "Meta/StrataLint/Golden/Frozen/events.jsonl";

    public static FrozenLedgerChangeOutcome Classify(RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(changes);
        var ledger = changes.Paths.Any(static path => path.Value == LedgerPath);
        var harness = changes.Paths.Any(static path =>
            path.Value.StartsWith("Meta/StrataLint/", StringComparison.Ordinal)
            && path.Value != LedgerPath);
        if (ledger && harness)
        {
            return new FrozenLedgerChangeOutcome.ForbiddenMixed(changes.Paths);
        }

        if (ledger)
        {
            return new FrozenLedgerChangeOutcome.LedgerOnly();
        }

        return harness
            ? new FrozenLedgerChangeOutcome.HarnessOnly()
            : new FrozenLedgerChangeOutcome.NoLedgerChange();
    }
}
