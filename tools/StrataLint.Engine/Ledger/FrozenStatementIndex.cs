using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum FrozenStatementResolutionFailure
{
    Unresolved,
    MissingDeclaration,
    AmbiguousDeclaration,
}

internal sealed class FrozenStatementIndex
{
    private readonly FrozenStateCatalog state;
    private readonly LeanAxiomReport report;

    private FrozenStatementIndex(FrozenStateCatalog state, LeanAxiomReport report)
    {
        this.state = state;
        this.report = report;
    }

    internal static FrozenStatementIndex Create(FrozenStateCatalog state, LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(state);
        ArgumentNullException.ThrowIfNull(report);
        return new FrozenStatementIndex(state, report);
    }

    internal bool ContainsModule(RepoPath path) => state.Records.ContainsKey(path);

    internal bool TryResolve(Gid gid, out StatementId? statementId, out string message)
        => TryResolve(gid, out statementId, out message, out _);

    internal bool TryResolve(
        Gid gid,
        out StatementId? statementId,
        out string message,
        out FrozenStatementResolutionFailure failure)
    {
        ArgumentNullException.ThrowIfNull(gid);
        statementId = null;
        failure = FrozenStatementResolutionFailure.Unresolved;
        if (gid.ToTarget() is not Target.Formal formal)
        {
            message = $"coverage GID is not a formal target: {gid.Value}";
            return false;
        }

        if (!state.Records.TryGetValue(formal.Path, out var frozen))
        {
            message = $"host module is not a member of frozen state: {formal.Path.Value}";
            return false;
        }

        if (formal.Declaration is null)
        {
            statementId = frozen.StatementId;
            message = string.Empty;
            return true;
        }

        if (!report.Files.TryGetValue(formal.Path, out var module)
            || !string.IsNullOrEmpty(module.Error))
        {
            message = $"coverage GID resolves to 0 current report declarations: {gid.Value}";
            return false;
        }

        var matches = ImmutableArray.CreateBuilder<StatementId>();
        foreach (var declaration in CanonicalStatementWriter.DeclarationStatementIds(
                     formal.Path,
                     module))
        {
            string decoded;
            int consumedCharacters;
            try
            {
                decoded = CanonicalLeanNameDecoder.DecodePrefix(
                    declaration.DeclarationNameKey,
                    0,
                    out consumedCharacters);
            }
            catch (FormatException)
            {
                message = $"current report declaration has an invalid name key: {formal.Path.Value}";
                return false;
            }

            if (consumedCharacters != declaration.DeclarationNameKey.Length)
            {
                message = $"current report declaration has an invalid name key: {formal.Path.Value}";
                return false;
            }

            var separator = decoded.LastIndexOf('.');
            var shortName = decoded[(separator + 1)..];
            if (string.Equals(shortName, formal.Declaration, StringComparison.Ordinal))
            {
                if (!CanonicalLeanNameDecoder.IsRepositoryNameKey(declaration.DeclarationNameKey))
                {
                    message = $"current report target declaration has an invalid name key: "
                        + formal.Path.Value;
                    return false;
                }

                matches.Add(declaration.StatementId);
            }
        }

        if (matches.Count != 1)
        {
            failure = matches.Count == 0
                ? FrozenStatementResolutionFailure.MissingDeclaration
                : FrozenStatementResolutionFailure.AmbiguousDeclaration;
            message = $"coverage GID resolves to {matches.Count} current report declarations: {gid.Value}";
            return false;
        }

        statementId = matches[0];
        message = string.Empty;
        return true;
    }
}
