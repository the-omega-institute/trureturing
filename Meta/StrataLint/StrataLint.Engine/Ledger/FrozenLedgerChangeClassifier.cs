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

    // 一节点一文件的冻结账本落位。此谓词先行加入 base 侧,使后续迁移 PR 的
    // baseline admission 能对 accepted/ 目录豁免 SL-003 容量阈 —— 否则
    // 「要豁免才能放文件,而放文件那次 PR 的法官还没有豁免」形成引导死结。
    public const string AcceptedRoot = "Meta/StrataLint/Golden/Frozen/accepted";

    public static bool IsAcceptedEventPath(string path) =>
        path.StartsWith(AcceptedRoot + "/", StringComparison.Ordinal)
        && path.EndsWith(".json", StringComparison.Ordinal)
        && path.AsSpan(AcceptedRoot.Length + 1, path.Length - AcceptedRoot.Length - 6)
            .IndexOf('/') < 0;

    // 文件名承载**裸摘要**,不含 "sha256:" 前缀。两条理由:
    // ① 冒号在 Windows 上是保留字符,带冒号的路径无法 check out;
    // ② 仓内既有的内容寻址先例 Meta/Digestion/atoms/sha256/<64hex> 同样是
    //    「目录名承载算法、文件名是裸摘要」。
    // 这是文件名约定的唯一真源:写盘与校验都必须经由它,不得各自拼字符串。
    public static string AcceptedFileName(string identity) =>
        (identity.StartsWith(DigestPrefix, StringComparison.Ordinal)
            ? identity[DigestPrefix.Length..]
            : identity) + ".json";

    public static string AcceptedPath(string identity) =>
        AcceptedRoot + "/" + AcceptedFileName(identity);

    private const string DigestPrefix = "sha256:";
}
