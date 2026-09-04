using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace StrataLint.Engine;

internal sealed record FrozenStateRecord(StatementId StatementId)
{
    internal static ImmutableArray<byte> Encode(StatementId statementId)
    {
        ArgumentNullException.ThrowIfNull(statementId);
        if (!FrozenHashSyntax.IsSha256(statementId.Value))
        {
            throw new ArgumentException(
                "Frozen state statement_id must be sha256 followed by 64 lowercase hexadecimal digits.",
                nameof(statementId));
        }

        var json = JsonSerializer.SerializeToUtf8Bytes(new EncodedRecord(statementId.Value));
        var bytes = ImmutableArray.CreateBuilder<byte>(json.Length + 1);
        bytes.AddRange(json);
        bytes.Add((byte)'\n');
        return bytes.ToImmutable();
    }

    private sealed record EncodedRecord(
        [property: JsonPropertyName("statement_id")] string StatementId);
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
            {
                throw new FormatException("path does not decode to a canonical D5 Lean selector");
            }

            var bytes = file.RawBytes.AsSpan();
            if (bytes.Length >= 3
                && bytes[0] == 0xef
                && bytes[1] == 0xbb
                && bytes[2] == 0xbf)
            {
                throw new FormatException("UTF-8 BOM is forbidden");
            }

            _ = StrictUtf8.GetString(bytes);
            if (bytes.Length < 2
                || bytes[^1] != (byte)'\n'
                || bytes[..^1].Contains((byte)'\n')
                || bytes.Contains((byte)'\r'))
            {
                throw new FormatException("record must be one JSON line terminated by exactly one LF");
            }

            using var document = JsonDocument.Parse(bytes[..^1].ToArray());
            if (document.RootElement.ValueKind is not JsonValueKind.Object)
            {
                throw new FormatException("record root must be a JSON object");
            }

            var properties = document.RootElement.EnumerateObject().ToArray();
            if (properties.Length != 1
                || !string.Equals(properties[0].Name, "statement_id", StringComparison.Ordinal))
            {
                throw new FormatException("record keys must be exactly {statement_id}");
            }

            if (properties[0].Value.ValueKind is not JsonValueKind.String
                || properties[0].Value.GetString() is not { } value
                || !FrozenHashSyntax.IsSha256(value))
            {
                throw new FormatException(
                    "statement_id must be sha256 followed by 64 lowercase hexadecimal digits");
            }

            var record = new FrozenStateRecord(StatementId.Create(value));
            if (!bytes.SequenceEqual(FrozenStateRecord.Encode(record.StatementId).AsSpan()))
            {
                throw new FormatException("record is not in canonical JSON byte form");
            }

            return record;
        }
        catch (Exception exception) when (
            exception is DecoderFallbackException or JsonException or FormatException)
        {
            throw new FormatException(
                $"Frozen state {file.Path.Value}: {exception.Message}",
                exception);
        }
    }
}

internal sealed class FrozenStateCatalog
{
    private FrozenStateCatalog(ImmutableDictionary<RepoPath, FrozenStateRecord> records) =>
        Records = records;

    internal ImmutableDictionary<RepoPath, FrozenStateRecord> Records { get; }

    internal static FrozenStateCatalog Load(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var records = ImmutableDictionary.CreateBuilder<RepoPath, FrozenStateRecord>();
        foreach (var file in snapshot.Files.Values
            .Where(static file => FrozenStatePath.IsUnderRoot(file.Path.Value))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal))
        {
            if (!FrozenStatePath.TryToModulePath(file.Path.Value, out var modulePath))
            {
                throw new FormatException(
                    $"Frozen state {file.Path.Value}: path does not decode to a canonical D5 Lean selector");
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
