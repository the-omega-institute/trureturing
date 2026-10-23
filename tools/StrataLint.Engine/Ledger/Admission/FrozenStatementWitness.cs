using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed class FrozenStatementWitness(
    ImmutableDictionary<RepoPath, ImmutableArray<FrozenDeclarationStatement>> modules)
{
    internal bool TryAuthenticate(RepoPath path, FrozenStateRecord protectedRecord,
        out ImmutableArray<FrozenDeclarationStatement> statements)
    {
        statements = [];
        if (!modules.TryGetValue(path, out var rows)
            || rows.Select(static row => row.DeclarationNameKey).Distinct(StringComparer.Ordinal).Count() != rows.Length
            || !rows.Select(static row => new FrozenDeclaration(row.DeclarationNameKey, row.Kind))
                .SequenceEqual(protectedRecord.Declarations)
            || FrozenContentAddress.ComputeModuleStatementId(path, rows) != protectedRecord.StatementId)
            return false;
        statements = rows;
        return true;
    }
}
