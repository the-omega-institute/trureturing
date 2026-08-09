using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Cli;

public abstract record DagLedgerLoadOutcome
{
    private DagLedgerLoadOutcome() { }

    public sealed record Loaded(FrozenLedgerSyntax Syntax) : DagLedgerLoadOutcome;

    public sealed record Invalid(string Message) : DagLedgerLoadOutcome;
}

public sealed record DagLedgerFileEvent(
    string Identity,
    string EventHash,
    string EventType,
    JsonElement Payload,
    int SchemaVersion,
    FrozenLedgerLineSyntax Syntax);

public abstract record DagLedgerFilesLoadOutcome
{
    private DagLedgerFilesLoadOutcome() { }

    public sealed record Loaded(ImmutableArray<DagLedgerFileEvent> Events) : DagLedgerFilesLoadOutcome;

    public sealed record Invalid(string Message) : DagLedgerFilesLoadOutcome;
}

public static class DagLedgerLoader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static DagLedgerLoadOutcome Load(ReadOnlySpan<byte> bytes)
    {
        try
        {
            _ = StrictUtf8.GetString(bytes);
            var raw = ImmutableArray.CreateRange(bytes.ToArray());
            var lines = ImmutableArray.CreateBuilder<FrozenLedgerLineSyntax>();
            var start = 0;
            for (var index = 0; index < bytes.Length; index++)
            {
                if (bytes[index] != (byte)'\n')
                {
                    continue;
                }

                var lineBytes = bytes[start..(index + 1)].ToArray();
                if (lineBytes.Length == 1 || lineBytes.AsSpan().Contains((byte)'\r'))
                {
                    throw new FormatException("Frozen ledger contains a blank or CR-terminated line.");
                }

                using var document = JsonDocument.Parse(lineBytes.AsMemory(0, lineBytes.Length - 1));
                if (document.RootElement.ValueKind != JsonValueKind.Object)
                {
                    throw new FormatException("Frozen ledger line must be a JSON object.");
                }

                lines.Add(new FrozenLedgerLineSyntax(
                    ImmutableArray.CreateRange(lineBytes),
                    document.RootElement.Clone()));
                start = index + 1;
            }

            if (start != bytes.Length)
            {
                var lineBytes = bytes[start..].ToArray();
                using var document = JsonDocument.Parse(lineBytes);
                if (document.RootElement.ValueKind != JsonValueKind.Object)
                {
                    throw new FormatException("Frozen ledger line must be a JSON object.");
                }

                lines.Add(new FrozenLedgerLineSyntax(
                    ImmutableArray.CreateRange(lineBytes),
                    document.RootElement.Clone()));
            }

            return new DagLedgerLoadOutcome.Loaded(new FrozenLedgerSyntax(raw, lines.ToImmutable()));
        }
        catch (Exception exception) when (exception is DecoderFallbackException or JsonException or FormatException)
        {
            return new DagLedgerLoadOutcome.Invalid(exception.Message);
        }
    }

    public static DagLedgerFilesLoadOutcome LoadFiles(IEnumerable<RepositoryFile> files)
    {
        ArgumentNullException.ThrowIfNull(files);
        try
        {
            var events = ImmutableArray.CreateBuilder<DagLedgerFileEvent>();
            var identities = new HashSet<string>(StringComparer.Ordinal);
            var hashes = new HashSet<string>(StringComparer.Ordinal);
            foreach (var file in files.OrderBy(static file => file.Path.Value, StringComparer.Ordinal))
            {
                var bytes = file.RawBytes.AsSpan();
                _ = StrictUtf8.GetString(bytes);
                if (bytes.Length < 2
                    || bytes[^1] != (byte)'\n'
                    || bytes[..^1].Contains((byte)'\n')
                    || bytes.Contains((byte)'\r'))
                {
                    throw new FormatException(
                        "Content-addressed frozen event file must contain exactly one LF-terminated JSON object.");
                }

                using var document = JsonDocument.Parse(bytes[..^1].ToArray());
                if (!FrozenLedgerCanonicalWriter.ValidateDagEvent(
                    document.RootElement,
                    out var identity,
                    out var eventHash,
                    out var validationMessage))
                {
                    throw new FormatException(validationMessage);
                }

                if (!hashes.Add(eventHash))
                {
                    throw new FormatException("Content-addressed frozen event event_hash is duplicated.");
                }

                if (!identities.Add(identity))
                {
                    throw new FormatException("Content-addressed frozen event identity is duplicated.");
                }

                // 文件名承载裸摘要,不含 "sha256:" 前缀:冒号在 Windows 上是保留字符,
                // 带冒号的路径无法 check out;仓内既有内容寻址先例 Meta/Digestion/atoms/sha256/<64hex>
                // 也是「目录名承载算法、文件名是裸摘要」。
                var fileName = file.Path.Value[(file.Path.Value.LastIndexOf('/') + 1)..];
                if (!string.Equals(
                        fileName,
                        FrozenLedgerChangeClassifier.AcceptedFileName(identity),
                        StringComparison.Ordinal))
                {
                    throw new FormatException("Content-addressed frozen event file name does not match event identity.");
                }

                var value = document.RootElement.Clone();
                events.Add(new DagLedgerFileEvent(
                    identity,
                    eventHash,
                    value.GetProperty("event_type").GetString()!,
                    value.GetProperty("payload").Clone(),
                    value.GetProperty("schema_version").GetInt32(),
                    new FrozenLedgerLineSyntax(ImmutableArray.CreateRange(bytes.ToArray()), value)));
            }

            return new DagLedgerFilesLoadOutcome.Loaded(events.ToImmutable());
        }
        catch (Exception exception) when (exception is DecoderFallbackException or JsonException or FormatException)
        {
            return new DagLedgerFilesLoadOutcome.Invalid(exception.Message);
        }
    }

    public static string? ValidateClosedDag(ImmutableArray<DagLedgerFileEvent> events)
    {
        var genesis = events.Where(static item => item.EventType == "Genesis").ToArray();
        if (genesis.Length != 1)
        {
            return "Content-addressed frozen ledger must contain exactly one Genesis.";
        }

        return TryOrderClosedDag(events, ImmutableArray<string>.Empty, out _)
            ? null
            : "Frozen event files do not form a closed dependency DAG.";
    }

    public static bool TryOrderClosedDag(
        ImmutableArray<DagLedgerFileEvent> events,
        ImmutableArray<string> preferredIdentityPrefix,
        out ImmutableArray<DagLedgerFileEvent> ordered)
    {
        var byIdentity = events.ToDictionary(static item => item.Identity, StringComparer.Ordinal);
        var remaining = events.OrderBy(static item => item.Identity, StringComparer.Ordinal).ToList();
        var result = ImmutableArray.CreateBuilder<DagLedgerFileEvent>(events.Length);
        var placedIdentities = new HashSet<string>(StringComparer.Ordinal);
        var placedHashes = new HashSet<string>(StringComparer.Ordinal);
        if (preferredIdentityPrefix.IsEmpty)
        {
            var genesis = events.Where(static item => item.EventType == "Genesis").ToArray();
            if (genesis.Length != 1)
            {
                ordered = ImmutableArray<DagLedgerFileEvent>.Empty;
                return false;
            }

            Place(genesis[0], remaining, result, placedIdentities, placedHashes);
        }

        foreach (var identity in preferredIdentityPrefix)
        {
            if (!byIdentity.TryGetValue(identity, out var item)
                || !CanPlace(item, result.Count, placedIdentities, placedHashes))
            {
                ordered = ImmutableArray<DagLedgerFileEvent>.Empty;
                return false;
            }

            Place(item, remaining, result, placedIdentities, placedHashes);
        }

        while (remaining.Count > 0)
        {
            var index = remaining.FindIndex(item =>
                CanPlace(item, result.Count, placedIdentities, placedHashes));
            if (index < 0)
            {
                ordered = ImmutableArray<DagLedgerFileEvent>.Empty;
                return false;
            }

            Place(remaining[index], remaining, result, placedIdentities, placedHashes);
        }

        ordered = result.MoveToImmutable();
        return true;
    }

    private static bool CanPlace(
        DagLedgerFileEvent item,
        int placedCount,
        HashSet<string> placedIdentities,
        HashSet<string> placedHashes) =>
        item.EventType == "Genesis"
            ? placedCount == 0
            : DependenciesPlaced(item, placedIdentities, placedHashes);

    private static void Place(
        DagLedgerFileEvent item,
        List<DagLedgerFileEvent> remaining,
        ImmutableArray<DagLedgerFileEvent>.Builder ordered,
        HashSet<string> placedIdentities,
        HashSet<string> placedHashes)
    {
        remaining.Remove(item);
        ordered.Add(item);
        placedIdentities.Add(item.Identity);
        placedHashes.Add(item.EventHash);
    }

    private static bool DependenciesPlaced(
        DagLedgerFileEvent item,
        HashSet<string> placedIdentities,
        HashSet<string> placedHashes)
    {
        if (item.EventType == "Freeze")
        {
            if (!item.Payload.TryGetProperty("prerequisite_frozen_node_ids", out var prerequisites)
                || prerequisites.ValueKind != JsonValueKind.Array)
            {
                return false;
            }

            return prerequisites.EnumerateArray().All(prerequisite =>
                prerequisite.ValueKind == JsonValueKind.String
                && placedIdentities.Contains(prerequisite.GetString()!));
        }

        if (item.EventType == "Reattest")
        {
            return item.Payload.TryGetProperty("previous_attestation_event_hash", out var previous)
                && previous.ValueKind == JsonValueKind.String
                && placedHashes.Contains(previous.GetString()!);
        }

        return true;
    }

    // v2 目录事件 → v1 线性 syntax 的唯一转换处。稳态校验与保守扩展都经由它,
    // 不得各自再抄一份(否则两处对 previous_attestation_event_hash 的重映射会分叉)。
    internal static FrozenLedgerSyntax ToLinearSyntax(ImmutableArray<DagLedgerFileEvent> events)
    {
        var raw = ImmutableArray.CreateBuilder<byte>();
        var lines = ImmutableArray.CreateBuilder<FrozenLedgerLineSyntax>();
        var previous = FrozenLedgerCanonicalWriter.ZeroHash;
        var dagToLinearHash = new Dictionary<string, string>(StringComparer.Ordinal);
        for (var sequence = 0; sequence < events.Length; sequence++)
        {
            var item = events[sequence];
            var payload = item.Payload;
            if (payload.TryGetProperty("previous_attestation_event_hash", out var dagPrevious))
            {
                var rewritten = JsonNode.Parse(payload.GetRawText())!.AsObject();
                rewritten["previous_attestation_event_hash"] = dagToLinearHash[dagPrevious.GetString()!];
                payload = JsonSerializer.SerializeToElement(rewritten);
            }

            var encoded = FrozenLedgerCanonicalWriter.WriteEvent(
                item.EventType,
                payload,
                previous,
                sequence);
            using var document = JsonDocument.Parse(encoded.Bytes.AsSpan()[..^1].ToArray());
            var line = new FrozenLedgerLineSyntax(encoded.Bytes, document.RootElement.Clone());
            raw.AddRange(encoded.Bytes);
            lines.Add(line);
            dagToLinearHash.Add(item.EventHash, encoded.Hash);
            previous = encoded.Hash;
        }

        return new FrozenLedgerSyntax(raw.ToImmutable(), lines.ToImmutable());
    }

}
