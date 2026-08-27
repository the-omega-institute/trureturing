using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal static class CanonicalStatementWriter
{
    // Lean's report already carries the canonical elaborated statement bytes.
    // This address intentionally excludes declaration/module identity so a
    // Frontier declaration can be compared with its delivered F declaration.
    internal static string StatementTypeAddress(string typeRepresentation) =>
        FrozenContentHash.Compute(
            FrozenHashDomains.Statement,
            Encoding.UTF8.GetBytes(typeRepresentation).AsSpan());

    internal static string StatementTypeAddress(LeanDeclaration declaration) =>
        declaration.StatementTypeAddress;

    internal static ImmutableArray<FrozenDeclarationStatement> DeclarationStatementIds(
        RepoPath path,
        LeanFileReport report) =>
        report.Declarations
            .Where(static declaration => declaration.IncludeInStatement)
            .Select(declaration => new FrozenDeclarationStatement(
                declaration.NameKey,
                declaration.Kind,
                StatementId.Create(DeclarationStatementId(path, declaration))))
            .OrderBy(static declaration => declaration.DeclarationNameKey, StringComparer.Ordinal)
            .ThenBy(static declaration => declaration.Kind, StringComparer.Ordinal)
            .ThenBy(static declaration => declaration.StatementId.Value, StringComparer.Ordinal)
            .ToImmutableArray();

    internal static string DeclarationStatementId(RepoPath path, LeanDeclaration declaration) =>
        declaration.PrecomputedStatementId
        ?? FrozenContentHash.Compute(
            FrozenHashDomains.Statement,
            WriteDeclaration(path, declaration).AsSpan());

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
            statement_material = declaration.LoadTypeRepresentation(),
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }
}
