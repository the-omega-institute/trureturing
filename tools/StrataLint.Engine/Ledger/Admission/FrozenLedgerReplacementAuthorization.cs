using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record FrozenLedgerReplacementAuthorizationContext(
    FrozenLedgerReplacementRecognition Recognition,
    FrozenLedgerBaseView BaseView,
    FrozenMaterialCatalog CandidateCatalog);

internal interface IFrozenLedgerReplacementAuthorization
{
    bool IsAuthorized(FrozenLedgerReplacementAuthorizationContext context);
}

/// 默认授权者:一律拒绝。
/// Ledger v5 是唯一 schema 之后,只有 <see cref="FrozenLedgerIncrementalReplacementRecognition"/>
/// 配 mathlib 升级谓词这一条合法替换路径;其余情形没有授权者,fail-closed。
internal sealed class RejectFrozenLedgerReplacementAuthorization
    : IFrozenLedgerReplacementAuthorization
{
    internal static RejectFrozenLedgerReplacementAuthorization Instance { get; } = new();

    private RejectFrozenLedgerReplacementAuthorization() { }

    public bool IsAuthorized(FrozenLedgerReplacementAuthorizationContext context)
    {
        ArgumentNullException.ThrowIfNull(context);
        return false;
    }
}
