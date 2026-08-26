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

    public static DagLedgerFilesLoadOutcome LoadFiles(IEnumerable<RepositoryFile> files) =>
        FrozenAcceptedEventLoader.LoadFiles(files);

    internal static DagLedgerFilesLoadOutcome LoadTrustedFiles(IEnumerable<RepositoryFile> files) =>
        FrozenAcceptedEventLoader.LoadTrustedFiles(files);

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

    internal static bool TryOrderIncrementalDag(
        ImmutableArray<DagLedgerFileEvent> events,
        IReadOnlySet<string> knownIdentities,
        IReadOnlySet<string> knownHashes,
        out ImmutableArray<DagLedgerFileEvent> ordered)
    {
        var remaining = events.OrderBy(static item => item.Identity, StringComparer.Ordinal).ToList();
        var result = ImmutableArray.CreateBuilder<DagLedgerFileEvent>(events.Length);
        var placedIdentities = knownIdentities.ToHashSet(StringComparer.Ordinal);
        var placedHashes = knownHashes.ToHashSet(StringComparer.Ordinal);
        while (remaining.Count > 0)
        {
            var index = remaining.FindIndex(item =>
                CanPlace(item, placedCount: 1, placedIdentities, placedHashes));
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
        if (item.Payload.TryGetProperty("frozen_node_id", out var frozenNodeId)
            && frozenNodeId.ValueKind == JsonValueKind.String)
        {
            placedIdentities.Add(frozenNodeId.GetString()!);
        }
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

        if (item.EventType == FrozenLedger.SupersedeEventType)
        {
            return item.Payload.TryGetProperty("previous_attestation_event_hash", out var previous)
                && previous.ValueKind == JsonValueKind.String
                && placedHashes.Contains(previous.GetString()!)
                && item.Payload.TryGetProperty("prerequisite_frozen_node_ids", out var prerequisites)
                && prerequisites.ValueKind == JsonValueKind.Array
                && prerequisites.EnumerateArray().All(prerequisite =>
                    prerequisite.ValueKind == JsonValueKind.String
                    && placedIdentities.Contains(prerequisite.GetString()!));
        }

        if (item.EventType == "Revoke")
        {
            return item.Payload.TryGetProperty("evidence", out var evidence)
                && evidence.ValueKind == JsonValueKind.Array
                && evidence.EnumerateArray().All(entry =>
                    entry.ValueKind == JsonValueKind.Object
                    && entry.TryGetProperty("root_frozen_node_id", out var root)
                    && root.ValueKind == JsonValueKind.String
                    && placedIdentities.Contains(root.GetString()!));
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
            var line = new FrozenLedgerLineSyntax(
                encoded.Bytes,
                document.RootElement.Clone(),
                item.EventHash);
            raw.AddRange(encoded.Bytes);
            lines.Add(line);
            dagToLinearHash.Add(item.EventHash, encoded.Hash);
            previous = encoded.Hash;
        }

        return new FrozenLedgerSyntax(raw.ToImmutable(), lines.ToImmutable());
    }

}
