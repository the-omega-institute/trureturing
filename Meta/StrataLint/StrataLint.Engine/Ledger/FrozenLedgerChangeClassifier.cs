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
    public const string LedgerPath = "Meta/StrataLint/Golden/Frozen/accepted";

    public static bool IsAcceptedEventPath(string path) =>
        path.StartsWith(LedgerPath + "/", StringComparison.Ordinal)
        && path.EndsWith(".json", StringComparison.Ordinal)
        && path.AsSpan(LedgerPath.Length + 1, path.Length - LedgerPath.Length - 6)
            .IndexOf('/') < 0;
}
