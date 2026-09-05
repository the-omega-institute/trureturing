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
