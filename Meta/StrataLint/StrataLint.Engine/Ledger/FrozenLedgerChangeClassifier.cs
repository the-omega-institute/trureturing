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
    // 一节点一文件的冻结账本落位:目录即账本,文件名即节点身份。
    public const string AcceptedRoot = "Meta/StrataLint/Golden/Frozen/accepted";

    public static bool IsAcceptedEventPath(string path) =>
        path.StartsWith(AcceptedRoot + "/", StringComparison.Ordinal)
        && path.EndsWith(".json", StringComparison.Ordinal)
        && path.AsSpan(AcceptedRoot.Length + 1, path.Length - AcceptedRoot.Length - 6)
            .IndexOf('/') < 0;
}
