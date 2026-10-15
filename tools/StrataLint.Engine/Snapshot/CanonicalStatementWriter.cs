using System.Collections.Immutable;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal static class CanonicalStatementWriter
{
    private static readonly JsonSerializerOptions StringOptions = new()
    {
        Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

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
        using var material = new MemoryStream();
        material.Write("{\"declaration_name_key\": "u8);
        WriteString(material, declaration.NameKey);
        material.Write(", \"kind\": "u8);
        WriteString(material, declaration.Kind);
        material.Write(", \"module_path\": "u8);
        WriteString(material, path.Value);
        material.Write(", \"schema\": \"declaration-statement-v1\", \"statement_material\": "u8);
        WriteString(material, declaration.LoadTypeRepresentation());
        material.Write("}\n"u8);
        return ImmutableArray.CreateRange(material.ToArray());
    }

    private static void WriteString(Stream output, string value)
    {
        output.WriteByte((byte)'"');
        for (var offset = 0; offset < value.Length;)
        {
            var length = Math.Min(65536, value.Length - offset);
            if (offset + length < value.Length
                && char.IsHighSurrogate(value[offset + length - 1])
                && char.IsLowSurrogate(value[offset + length]))
                length--;
            var encoded = JsonSerializer.SerializeToUtf8Bytes(value.Substring(offset, length), StringOptions);
            output.Write(encoded.AsSpan(1, encoded.Length - 2));
            offset += length;
        }
        output.WriteByte((byte)'"');
    }
}
