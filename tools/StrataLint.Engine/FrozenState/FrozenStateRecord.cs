using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal sealed record FrozenDeclaration(
    [property: JsonPropertyName("declaration_name_key")] string DeclarationNameKey,
    [property: JsonPropertyName("kind")] string Kind);

internal sealed record FrozenStateRecord(StatementId StatementId, ImmutableArray<FrozenDeclaration> Declarations)
{
    internal static ImmutableArray<FrozenDeclaration> Project(LeanFileReport report) => report.Declarations
        .Where(static declaration => declaration.IncludeInStatement)
        .Select(static declaration => new FrozenDeclaration(declaration.NameKey, declaration.Kind))
        .OrderBy(static declaration => declaration.DeclarationNameKey, StringComparer.Ordinal)
        .ThenBy(static declaration => declaration.Kind, StringComparer.Ordinal).ToImmutableArray();

    internal static FrozenStateRecord FromReport(RepoPath path, LeanFileReport report) => new(
        FrozenContentAddress.ComputeModuleStatementId(path, report), Project(report));

    internal static ImmutableArray<byte> Encode(StatementId statementId,
        ImmutableArray<FrozenDeclaration> declarations = default)
    {
        ArgumentNullException.ThrowIfNull(statementId);
        if (!FrozenHashSyntax.IsSha256(statementId.Value))
            throw new ArgumentException("Frozen state statement_id must be sha256 followed by 64 lowercase hexadecimal digits.", nameof(statementId));
        if (declarations.IsDefault) declarations = [];
        ValidateDeclarations(declarations);
        var json = JsonSerializer.SerializeToUtf8Bytes(new EncodedRecord(statementId.Value, declarations));
        return ImmutableArray.CreateRange(json.Append((byte)'\n'));
    }

    internal static void ValidateDeclarations(ImmutableArray<FrozenDeclaration> declarations)
    {
        FrozenDeclaration? previous = null;
        foreach (var declaration in declarations)
        {
            if (!IsCanonicalNameKey(declaration.DeclarationNameKey)
                || !TruthExportValidation.DeclarationKinds.Contains(declaration.Kind))
                throw new FormatException("declarations must contain canonical declaration_name_key and report kind");
            if (previous is not null)
            {
                var nameOrder = StringComparer.Ordinal.Compare(previous.DeclarationNameKey, declaration.DeclarationNameKey);
                if (nameOrder > 0 || nameOrder == 0 && StringComparer.Ordinal.Compare(previous.Kind, declaration.Kind) >= 0)
                    throw new FormatException("declarations must be Ordinal sorted and unique by name key and kind");
            }
            previous = declaration;
        }
    }

    private static bool IsCanonicalNameKey(string key)
    {
        try
        {
            var components = CanonicalLeanNameDecoder.ComponentsPrefix(key, 0, out var consumed);
            return consumed == key.Length && components.Length > 0;
        }
        catch (FormatException) { return false; }
    }

    private sealed record EncodedRecord(
        [property: JsonPropertyName("statement_id")] string StatementId,
        [property: JsonPropertyName("declarations")] ImmutableArray<FrozenDeclaration> Declarations);
}

internal static class FrozenStateRecordLoader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static FrozenStateRecord Load(RepositoryFile file)
    {
        ArgumentNullException.ThrowIfNull(file);
        try
        {
            if (!FrozenStatePath.TryToModulePath(file.Path.Value, out _))
                throw new FormatException("path must encode exactly one canonical repository Lean module");
            var bytes = file.RawBytes.AsSpan();
            if (bytes.Length >= 3 && bytes[0] == 0xef && bytes[1] == 0xbb && bytes[2] == 0xbf)
                throw new FormatException("UTF-8 BOM is forbidden");
            _ = StrictUtf8.GetString(bytes);
            if (bytes.Length < 2 || bytes[^1] != (byte)'\n' || bytes[..^1].Contains((byte)'\n') || bytes.Contains((byte)'\r'))
                throw new FormatException("record must be one JSON line terminated by exactly one LF");
            using var document = JsonDocument.Parse(bytes[..^1].ToArray());
            var root = document.RootElement;
            RequireKeys(root, ["statement_id", "declarations"], "record");
            if (root.GetProperty("statement_id").ValueKind is not JsonValueKind.String
                || root.GetProperty("statement_id").GetString() is not { } value || !FrozenHashSyntax.IsSha256(value))
                throw new FormatException("statement_id must be sha256 followed by 64 lowercase hexadecimal digits");
            var array = root.GetProperty("declarations");
            if (array.ValueKind is not JsonValueKind.Array) throw new FormatException("declarations must be an array");
            var declarations = ImmutableArray.CreateBuilder<FrozenDeclaration>();
            foreach (var item in array.EnumerateArray())
            {
                RequireKeys(item, ["declaration_name_key", "kind"], "declaration");
                if (item.GetProperty("declaration_name_key").ValueKind is not JsonValueKind.String
                    || item.GetProperty("kind").ValueKind is not JsonValueKind.String)
                    throw new FormatException("declaration fields must be strings");
                declarations.Add(new(item.GetProperty("declaration_name_key").GetString()!, item.GetProperty("kind").GetString()!));
            }
            var record = new FrozenStateRecord(StatementId.Create(value), declarations.ToImmutable());
            if (!bytes.SequenceEqual(FrozenStateRecord.Encode(record.StatementId, record.Declarations).AsSpan()))
                throw new FormatException("record is not in canonical JSON byte form");
            return record;
        }
        catch (Exception exception) when (exception is DecoderFallbackException or JsonException or FormatException)
        {
            throw new FormatException($"Frozen state {file.Path.Value}: {exception.Message}", exception);
        }
    }

    private static void RequireKeys(JsonElement element, string[] keys, string label)
    {
        if (element.ValueKind is not JsonValueKind.Object)
            throw new FormatException(label + " must be a JSON object");
        var properties = element.EnumerateObject().Select(static property => property.Name).ToArray();
        if (properties.Length != keys.Length || properties.Distinct(StringComparer.Ordinal).Count() != keys.Length
            || !properties.ToHashSet(StringComparer.Ordinal).SetEquals(keys))
            throw new FormatException(label + " keys must be exactly {" + string.Join(", ", keys) + "}");
    }
}

internal sealed class FrozenStateCatalog
{
    internal static readonly AsyncLocal<Action?> Loading = new();

    private FrozenStateCatalog(ImmutableDictionary<RepoPath, FrozenStateRecord> records) =>
        Records = records;

    internal ImmutableDictionary<RepoPath, FrozenStateRecord> Records { get; }

    internal ImmutableArray<RepoPath> Selectors => Records.Keys
        .OrderBy(static path => path.Value, StringComparer.Ordinal)
        .ToImmutableArray();

    internal static FrozenStateCatalog Load(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        Loading.Value?.Invoke();
        var records = ImmutableDictionary.CreateBuilder<RepoPath, FrozenStateRecord>();
        foreach (var file in snapshot.Files.Values
            .Where(static file => FrozenStatePath.IsUnderRoot(file.Path.Value))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal))
        {
            if (!FrozenStatePath.TryToModulePath(file.Path.Value, out var modulePath))
            {
                throw new FormatException(
                    $"Frozen state {file.Path.Value}: "
                    + "path must encode exactly one canonical repository Lean module");
            }

            var record = FrozenStateRecordLoader.Load(file);
            if (!records.TryAdd(modulePath, record))
            {
                throw new FormatException(
                    $"Frozen state {file.Path.Value}: selector {modulePath.Value} is duplicated");
            }
        }

        return new FrozenStateCatalog(records.ToImmutable());
    }
}
