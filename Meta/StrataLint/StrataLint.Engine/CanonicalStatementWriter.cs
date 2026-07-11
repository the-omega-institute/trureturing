using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static class CanonicalStatementWriter
{
    internal static ImmutableArray<FrozenDeclarationStatement> DeclarationStatementIds(
        RepoPath path,
        LeanFileReport report) =>
        report.Declarations
            .Where(static declaration => declaration.IncludeInStatement)
            .Select(declaration => new FrozenDeclarationStatement(
                declaration.NameKey,
                declaration.Kind,
                StatementId.Create(FrozenContentHash.Compute(
                    FrozenHashDomains.Statement,
                    WriteDeclaration(path, declaration).AsSpan()))))
            .OrderBy(static declaration => declaration.DeclarationNameKey, StringComparer.Ordinal)
            .ThenBy(static declaration => declaration.Kind, StringComparer.Ordinal)
            .ThenBy(static declaration => declaration.StatementId.Value, StringComparer.Ordinal)
            .ToImmutableArray();

    internal static ImmutableArray<byte> WriteModule(RepoPath path, LeanFileReport report)
    {
        return WriteModule(path, DeclarationStatementIds(path, report));
    }

    internal static ImmutableArray<byte> WriteModule(
        RepoPath path,
        ImmutableArray<FrozenDeclarationStatement> declarations)
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            declarations = declarations
                .Select(static declaration => new
                {
                    kind = declaration.Kind,
                    name_key = declaration.DeclarationNameKey,
                    statement_id = declaration.StatementId.Value,
                }),
            module_path = path.Value,
            schema = "module-statement-v1",
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }

    private static ImmutableArray<byte> WriteDeclaration(RepoPath path, LeanDeclaration declaration)
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            declaration_name_key = declaration.NameKey,
            kind = declaration.Kind,
            module_path = path.Value,
            schema = "declaration-statement-v1",
            statement_material = declaration.TypeRepresentation,
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }
}
