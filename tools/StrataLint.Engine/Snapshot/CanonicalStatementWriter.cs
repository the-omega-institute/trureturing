using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Encodings.Web;
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
        ?? DeclarationStatementId(path, declaration, new StringReader(declaration.LoadTypeRepresentation()));

    internal static string DeclarationStatementId(
        RepoPath path,
        LeanDeclaration declaration,
        TextReader statementMaterial)
    {
        using var algorithm = SHA256.Create();
        using var destination = new CryptoStream(Stream.Null, algorithm, CryptoStreamMode.Write, leaveOpen: true);
        destination.Write(Encoding.UTF8.GetBytes(FrozenHashDomains.Statement));
        WriteDeclaration(destination, path, declaration, statementMaterial);
        destination.FlushFinalBlock();
        return "sha256:" + Convert.ToHexStringLower(algorithm.Hash!);
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

    internal static void WriteDeclaration(
        Stream destination,
        RepoPath path,
        LeanDeclaration declaration,
        TextReader statementMaterial)
    {
        destination.Write("{\"declaration_name_key\": "u8);
        WriteString(destination, new StringReader(declaration.NameKey));
        destination.Write(", \"kind\": "u8);
        WriteString(destination, new StringReader(declaration.Kind));
        destination.Write(", \"module_path\": "u8);
        WriteString(destination, new StringReader(path.Value));
        destination.Write(", \"schema\": \"declaration-statement-v1\", \"statement_material\": "u8);
        WriteString(destination, statementMaterial);
        destination.Write("}\n"u8);
    }

    private static void WriteString(Stream destination, TextReader value)
    {
        const int chunkSize = 16384;
        var characters = new char[chunkSize + 1];
        var carried = 0;
        destination.Write("\""u8);
        while (true)
        {
            var read = value.Read(characters.AsSpan(carried, chunkSize));
            var count = carried + read;
            if (count == 0) break;
            carried = read > 0 && char.IsHighSurrogate(characters[count - 1]) ? 1 : 0;
            var encoded = JsonEncodedText.Encode(
                characters.AsSpan(0, count - carried), JavaScriptEncoder.UnsafeRelaxedJsonEscaping);
            destination.Write(encoded.EncodedUtf8Bytes);
            if (carried > 0) characters[0] = characters[count - 1];
            if (read == 0) break;
        }
        destination.Write("\""u8);
    }
}
