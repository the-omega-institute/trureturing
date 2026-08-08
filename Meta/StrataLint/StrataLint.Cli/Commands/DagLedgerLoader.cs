using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
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

    public static DagLedgerLoadOutcome LoadFiles(
        IEnumerable<(string Path, ReadOnlyMemory<byte> Bytes)> files)
    {
        try
        {
            var pending = files.Select(file => ParseFile(file.Path, file.Bytes)).ToList();
            var ordered = ImmutableArray.CreateBuilder<FrozenLedgerLineSyntax>(pending.Count);
            var hashes = new HashSet<string>(StringComparer.Ordinal);
            var nodeIds = new HashSet<string>(StringComparer.Ordinal);
            while (pending.Count > 0)
            {
                var eligible = pending
                    .Where(item => IsEligible(item.Value, ordered.Count == 0, hashes, nodeIds))
                    .OrderBy(item => item.Value.GetProperty("event_hash").GetString(), StringComparer.Ordinal)
                    .FirstOrDefault();
                if (eligible is null)
                {
                    throw new FormatException("Frozen event files do not form a closed dependency DAG.");
                }

                pending.Remove(eligible);
                ordered.Add(eligible);
                hashes.Add(eligible.Value.GetProperty("event_hash").GetString()!);
                if (eligible.Value.GetProperty("payload").TryGetProperty("frozen_node_id", out var id))
                {
                    nodeIds.Add(id.GetString()!);
                }
            }

            var lines = ordered.ToImmutable();
            return new DagLedgerLoadOutcome.Loaded(new FrozenLedgerSyntax(
                lines.SelectMany(static line => line.RawBytes).ToImmutableArray(),
                lines));
        }
        catch (Exception exception) when (exception is DecoderFallbackException or JsonException or FormatException)
        {
            return new DagLedgerLoadOutcome.Invalid(exception.Message);
        }
    }

    private static FrozenLedgerLineSyntax ParseFile(string path, ReadOnlyMemory<byte> bytes)
    {
        _ = StrictUtf8.GetString(bytes.Span);
        if (bytes.IsEmpty || bytes.Span[^1] != (byte)'\n' || bytes.Span.Contains((byte)'\r'))
        {
            throw new FormatException($"Frozen event file {path} must have one LF-terminated JSON object.");
        }

        using var document = JsonDocument.Parse(bytes[..^1]);
        var root = document.RootElement;
        if (root.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException($"Frozen event file {path} must contain a JSON object.");
        }

        if (!root.TryGetProperty("payload", out var payload)
            || payload.ValueKind != JsonValueKind.Object
            || !root.TryGetProperty("event_hash", out var eventHash)
            || eventHash.ValueKind != JsonValueKind.String)
        {
            throw new FormatException($"Frozen event file {path} is missing its payload or event_hash.");
        }

        var identity = payload.TryGetProperty("frozen_node_id", out var nodeId)
            ? nodeId.GetString()
            : eventHash.GetString();
        if (identity is null || !identity.StartsWith("sha256:", StringComparison.Ordinal))
        {
            throw new FormatException($"Frozen event file {path} has a malformed node identity.");
        }

        var expected = identity?[7..] + ".json";
        if (!string.Equals(Path.GetFileName(path), expected, StringComparison.Ordinal))
        {
            throw new FormatException($"Frozen event filename does not match its node identity: {path}.");
        }

        return new FrozenLedgerLineSyntax(
            ImmutableArray.CreateRange(bytes.ToArray()),
            root.Clone());
    }

    private static bool IsEligible(
        JsonElement root,
        bool first,
        HashSet<string> hashes,
        HashSet<string> nodeIds)
    {
        var type = root.GetProperty("event_type").GetString();
        var payload = root.GetProperty("payload");
        if (type == "Genesis") return first;
        if (first) return false;
        if (type == "Freeze")
        {
            return payload.GetProperty("prerequisite_frozen_node_ids")
                .EnumerateArray().All(item => nodeIds.Contains(item.GetString()!));
        }
        if (type == "Reattest")
        {
            return hashes.Contains(payload.GetProperty("previous_attestation_event_hash").GetString()!);
        }
        if (type == "Revoke")
        {
            return payload.GetProperty("root_frozen_node_ids")
                .EnumerateArray().All(item => nodeIds.Contains(item.GetString()!));
        }
        return true;
    }
}
