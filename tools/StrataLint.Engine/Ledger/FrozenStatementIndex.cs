using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed class FrozenStatementIndex
{
    private readonly ImmutableDictionary<RepoPath, FrozenActiveEntry> activeByPath;

    private FrozenStatementIndex(ImmutableDictionary<RepoPath, FrozenActiveEntry> activeByPath) =>
        this.activeByPath = activeByPath;

    internal static FrozenStatementIndex Load(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        return new FrozenStatementIndex(FrozenLedgerBaseViewReader.Read(snapshot).ActiveByPath);
    }

    internal bool ContainsModule(RepoPath path) => activeByPath.ContainsKey(path);

    internal bool TryResolve(Gid gid, out StatementId? statementId, out string message)
    {
        ArgumentNullException.ThrowIfNull(gid);
        statementId = null;
        if (gid.ToTarget() is not Target.Formal formal)
        {
            message = $"coverage GID is not a formal target: {gid.Value}";
            return false;
        }

        if (!activeByPath.TryGetValue(formal.Path, out var active))
        {
            message = $"host module is not active in the frozen ledger: {formal.Path.Value}";
            return false;
        }

        if (formal.Declaration is null)
        {
            statementId = active.Material.StatementId;
            message = string.Empty;
            return true;
        }

        var matches = ImmutableArray.CreateBuilder<StatementId>();
        foreach (var declaration in active.Material.DeclarationStatementIds)
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
                message = $"frozen declaration has an invalid name key: {formal.Path.Value}";
                return false;
            }

            if (consumedCharacters != declaration.DeclarationNameKey.Length)
            {
                message = $"frozen declaration has an invalid name key: {formal.Path.Value}";
                return false;
            }

            var separator = decoded.LastIndexOf('.');
            var shortName = decoded[(separator + 1)..];
            if (string.Equals(shortName, formal.Declaration, StringComparison.Ordinal))
            {
                if (!CanonicalLeanNameDecoder.IsRepositoryNameKey(declaration.DeclarationNameKey))
                {
                    message = $"frozen target declaration has an invalid name key: "
                        + formal.Path.Value;
                    return false;
                }

                matches.Add(declaration.StatementId);
            }
        }

        if (matches.Count != 1)
        {
            message = $"coverage GID resolves to {matches.Count} frozen declarations: {gid.Value}";
            return false;
        }

        statementId = matches[0];
        message = string.Empty;
        return true;
    }
}
