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

internal sealed class LegacyFrozenLedgerReplacementAuthorization
    : IFrozenLedgerReplacementAuthorization
{
    internal static LegacyFrozenLedgerReplacementAuthorization Instance { get; } = new();

    private LegacyFrozenLedgerReplacementAuthorization() { }

    public bool IsAuthorized(FrozenLedgerReplacementAuthorizationContext context)
    {
        ArgumentNullException.ThrowIfNull(context);
        return context.BaseView.Events.All(static item =>
                LegacyFrozenLedgerEventSemantics.IsLegacySchemaVersion(item.SchemaVersion))
            && !context.BaseView.ActiveByPath.IsEmpty
            && LegacyFrozenLedgerStatementIdentityContinuity.FirstMismatch(
                context.BaseView.ActiveByPath.Values.Select(static entry =>
                    LegacyFrozenStatementIdentity.From(entry.Material)),
                context.CandidateCatalog) is null;
    }
}

internal sealed record LegacyFrozenStatementIdentity(
    RepoPath Path,
    StatementId StatementId,
    ImmutableArray<FrozenDeclarationStatement> DeclarationStatementIds)
{
    internal static LegacyFrozenStatementIdentity From(FrozenNodeMaterial material) =>
        new(material.RepoPath, material.StatementId, material.DeclarationStatementIds);
}

internal static class LegacyFrozenLedgerStatementIdentityContinuity
{
    internal static RepoPath? FirstMismatch(
        IEnumerable<LegacyFrozenStatementIdentity> recordedIdentities,
        FrozenMaterialCatalog candidateCatalog)
    {
        ArgumentNullException.ThrowIfNull(recordedIdentities);
        ArgumentNullException.ThrowIfNull(candidateCatalog);
        var recordedByPath = recordedIdentities.ToDictionary(static item => item.Path);
        foreach (var material in candidateCatalog.ClosedNodes.OrderBy(
            static item => item.RepoPath.Value,
            StringComparer.Ordinal))
        {
            if (!recordedByPath.TryGetValue(material.RepoPath, out var recorded))
            {
                continue;
            }

            if (recorded.StatementId != material.StatementId
                || !recorded.DeclarationStatementIds.SequenceEqual(
                    material.DeclarationStatementIds))
            {
                return material.RepoPath;
            }
        }

        return null;
    }
}
