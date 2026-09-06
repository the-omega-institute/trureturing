using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Cli;

internal static class SettleAtomCommand
{
    private const string Usage = "USAGE: StrataLint settle-atom --request FILE --base REV | settle-atom --clear ATOM_ID --base REV";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static CommandResult Run(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments) =>
        Run(root, repository, arguments, BackfillInventoryWriter.WriteAtom, ReadRequest,
            static (directory, current, updates) => IngestCommand.ApplyLedgerUpdatesAtomically(directory, current, updates));

    internal static CommandResult Run(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments,
        Func<DigestionLedgerEntry, ImmutableArray<byte>> writeAtom,
        Func<string, string, ImmutableArray<byte>> readRequest,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>> applyUpdates)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(root);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(writeAtom);
        ArgumentNullException.ThrowIfNull(readRequest);
        ArgumentNullException.ThrowIfNull(applyUpdates);
        try
        {
            var options = ParseArguments(arguments);
            var request = options.RequestPath is null ? null : LoadRequest(readRequest(root, options.RequestPath));
            var atomId = request?.AtomId ?? options.ClearAtomId!;
            var current = repository.ReadCurrent();
            _ = repository.ReadRevision(options.BaseRevision);
            var snapshot = Decode(current);
            var document = BackfillInventoryLoader.Load(snapshot);
            var target = LocateTarget(document, atomId);
            DigestionLedgerEntry updated;
            if (request is null)
            {
                if (target.Receipts.Nonpropositional is null)
                    throw Invalid("NONPROPOSITIONAL_ABSENT", $"atom_id={atomId}");
                updated = target with
                {
                    Receipts = target.Receipts with { Nonpropositional = null },
                    ProjectedStatus = new(DigestionMigrationState.Residual, DigestionTruthState.Open),
                };
            }
            else
            {
                RequireWritable(target, document);
                var context = DigestionAtomContextProjection.Resolve(snapshot, document, atomId);
                if (context.Previous?.AtomId != request.PreviousAtomId || context.Next?.AtomId != request.NextAtomId)
                    throw Invalid("CONTEXT_MISMATCH", $"atom_id={atomId}");
                updated = target with
                {
                    Receipts = target.Receipts with { Nonpropositional = new(request.Justification, request.PreviousAtomId, request.NextAtomId) },
                    ProjectedStatus = new(DigestionMigrationState.Nonpropositional, DigestionTruthState.Inapplicable),
                };
            }
            var path = Write(root, current, target, updated, writeAtom, applyUpdates);
            var sentinel = request is null ? "SETTLE_CLEARED" : "SETTLED_NONPROPOSITIONAL";
            var output = $"{sentinel} atom_id={atomId} path={path}\n";
            if (request is not null)
            {
                var ancestors = CoveredAncestors(document, atomId);
                if (ancestors.Length > 0) output += "SETTLE_ALIGN_REQUIRED ancestors=" + string.Join(',', ancestors) + "\n";
            }
            return new CommandResult(true, output, string.Empty);
        }
        catch (DigestionAtomContextException error)
        {
            return new CommandResult(false, string.Empty, $"SETTLE_INVALID {error.Code} {error.Message}\n");
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"SETTLE_INVALID {error.Message}\n");
        }
    }

    private static void RequireWritable(DigestionLedgerEntry entry, BackfillInventoryDocument document)
    {
        if (entry.Receipts.Nonpropositional is not null
            || entry.ProjectedStatus != new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open))
            throw Invalid("NOT_RESIDUAL_OPEN", $"atom_id={entry.AtomId}");
        if (!entry.Coverage.IsEmpty) throw Invalid("COVERAGE_PRESENT", $"atom_id={entry.AtomId}");
        if (entry.Receipts.Quarantine is not null) throw Invalid("QUARANTINE_PRESENT", $"atom_id={entry.AtomId}");
        if (entry.Receipts.CoverDisposition is not null) throw Invalid("COVER_DISPOSITION_PRESENT", $"atom_id={entry.AtomId}");
        if (!entry.Receipts.UnresolvedSubitems.IsEmpty) throw Invalid("UNRESOLVED_SUBITEMS_PRESENT", $"atom_id={entry.AtomId}");
        var entries = document.RequireDigestionEntries();
        foreach (var child in entry.Receipts.ChainAtoms)
        {
            var matches = entries.Where(candidate => candidate.AtomId == child).ToArray();
            if (matches.Length != 1 || matches[0].ProjectedStatus.Migration is not
                (DigestionMigrationState.Absorbed or DigestionMigrationState.Nonpropositional))
                throw Invalid("CHAIN_OPEN", $"atom_id={entry.AtomId} child={child}");
        }
    }

    private static string Write(string root, RawRepositorySnapshot current, DigestionLedgerEntry original,
        DigestionLedgerEntry updated, Func<DigestionLedgerEntry, ImmutableArray<byte>> writeAtom,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>> applyUpdates)
    {
        var oldPath = AtomPath(original);
        var newPath = AtomPath(updated);
        if (current.Entries.Count(entry => entry.Path == oldPath) != 1)
            throw Invalid("SHARD_AMBIGUOUS", $"atom_id={original.AtomId} path={oldPath}");
        RawRepositorySnapshot final;
        try
        {
            var bytes = writeAtom(updated);
            final = RawRepositorySnapshot.Create(current.Entries.Where(entry => entry.Path != oldPath)
                .Append(new RawRepositoryEntry(newPath, bytes)));
            var replay = LocateTarget(BackfillInventoryLoader.Load(Decode(final)), updated.AtomId);
            if (!writeAtom(replay).AsSpan().SequenceEqual(bytes.AsSpan()))
                throw new FormatException("serialized shard did not replay byte-identically");
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            throw Invalid("ROUND_TRIP_FAILED", $"atom_id={updated.AtomId} {error.Message}");
        }
        applyUpdates(root, current, IngestCommand.LedgerUpdates(current, final));
        return newPath;
    }

    private static string[] CoveredAncestors(BackfillInventoryDocument document, string atomId)
    {
        var visited = new HashSet<string>(StringComparer.Ordinal) { atomId };
        var ancestors = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Queue<string>();
        pending.Enqueue(atomId);
        var entries = document.RequireDigestionEntries();
        while (pending.TryDequeue(out var child))
        {
            foreach (var parent in entries.Where(entry => entry.Receipts.ChainAtoms.Contains(child, StringComparer.Ordinal)))
            {
                if (!visited.Add(parent.AtomId)) continue;
                pending.Enqueue(parent.AtomId);
                if (!parent.Coverage.IsEmpty) ancestors.Add(parent.AtomId);
            }
        }
        return ancestors.Order(StringComparer.Ordinal).ToArray();
    }

    private static SettleRequest LoadRequest(ImmutableArray<byte> bytes)
    {
        if (bytes.IsEmpty || bytes[^1] != (byte)'\n' || bytes.AsSpan().Contains((byte)'\r')
            || bytes.AsSpan().StartsWith(Encoding.UTF8.Preamble))
            throw Invalid("REQUEST_ENCODING_INVALID", "request must be strict UTF-8 without BOM/CR and end in LF");
        string text;
        try { text = StrictUtf8.GetString(bytes.AsSpan()); }
        catch (DecoderFallbackException error) { throw Invalid("REQUEST_ENCODING_INVALID", error.Message); }
        TomlTable table;
        try { table = TomlSerializer.Deserialize<TomlTable>(text) ?? throw new FormatException("request is empty"); }
        catch (Exception error) when (error is not OutOfMemoryException) { throw Invalid("REQUEST_TOML_INVALID", error.Message); }
        if (!table.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(["atom_id", "justification", "previous_atom_id", "next_atom_id"]))
            throw Invalid("REQUEST_KEYS_INVALID", "request keys are not canonical");
        var atomId = RequiredString(table, "atom_id");
        if (!DigestionNonpropositional.IsAtomId(atomId)) throw Invalid("ARGUMENTS_INVALID", "atom_id must be a canonical atom id");
        return new SettleRequest(atomId, RequiredString(table, "justification"),
            Neighbor(table, "previous_atom_id"), Neighbor(table, "next_atom_id"));
    }

    private static string? Neighbor(TomlTable table, string key)
    {
        var value = RequiredString(table, key);
        if (value == "source-boundary") return null;
        if (!DigestionNonpropositional.IsAtomId(value))
            throw Invalid("ARGUMENTS_INVALID", $"{key} must be a canonical atom id or source-boundary");
        return value;
    }

    private static string RequiredString(TomlTable table, string key) =>
        table[key] is string value && !string.IsNullOrWhiteSpace(value) ? value.Trim()
            : throw Invalid("REQUEST_VALUE_BLANK", $"key={key}");

    private static ImmutableArray<byte> ReadRequest(string root, string requestedPath)
    {
        if (string.IsNullOrWhiteSpace(requestedPath) || requestedPath != requestedPath.Trim())
            throw Invalid("REQUEST_PATH_INVALID", "request path is blank or padded");
        var path = Path.GetFullPath(Path.Combine(root, requestedPath));
        var prefix = Path.TrimEndingDirectorySeparator(Path.GetFullPath(root)) + Path.DirectorySeparatorChar;
        if (!Path.IsPathFullyQualified(requestedPath) && !path.StartsWith(prefix, StringComparison.Ordinal))
            throw Invalid("REQUEST_PATH_INVALID", "repository-relative request escapes the repository");
        try { return [.. File.ReadAllBytes(path)]; }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException)
        { throw Invalid("REQUEST_UNREADABLE", error.Message); }
    }

    private static DigestionLedgerEntry LocateTarget(BackfillInventoryDocument document, string atomId)
    {
        var entries = document.RequireDigestionEntries().Where(entry => entry.AtomId == atomId).ToArray();
        return entries.Length switch
        {
            0 => throw Invalid("ATOM_ABSENT", $"atom_id={atomId}"),
            1 => entries[0],
            _ => throw Invalid("ATOM_AMBIGUOUS", $"atom_id={atomId}"),
        };
    }

    private static string AtomPath(DigestionLedgerEntry entry) => BackfillInventoryLoader.RootPath + entry.SourceId + "/"
        + DigestionStatusNames.Migration(entry.ProjectedStatus.Migration) + "-"
        + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth) + "/" + entry.AtomId + ".yaml";

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure error => throw new FormatException(error.Message),
    };

    private static InvalidOperationException Invalid(string code, string detail) => new(code + " " + detail);

    private static SettleOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        string? request = null, clear = null, baseline = null;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--request" when request is null && index + 1 < arguments.Count: request = arguments[++index]; break;
                case "--clear" when clear is null && index + 1 < arguments.Count: clear = arguments[++index]; break;
                case "--base" when baseline is null && index + 1 < arguments.Count: baseline = arguments[++index]; break;
                default: throw Invalid("ARGUMENTS_INVALID", Usage);
            }
        }
        if (string.IsNullOrWhiteSpace(baseline) || baseline != baseline.Trim() || (request is null) == (clear is null)
            || (clear is not null && !DigestionNonpropositional.IsAtomId(clear)))
            throw Invalid("ARGUMENTS_INVALID", Usage);
        return new SettleOptions(request, clear, baseline);
    }

    private sealed record SettleOptions(string? RequestPath, string? ClearAtomId, string BaseRevision);
    private sealed record SettleRequest(string AtomId, string Justification, string? PreviousAtomId, string? NextAtomId);
}
