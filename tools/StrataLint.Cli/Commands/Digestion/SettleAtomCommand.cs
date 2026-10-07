using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Cli;

internal static partial class SettleAtomCommand
{
    private const string Usage = "USAGE: StrataLint settle-atom --request FILE | settle-atom --clear ATOM_ID";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private sealed class Session
    {
        internal Session(IRepositoryGateway repository)
        {
            var loaded = DigestionWorkingTree.ReadLedger(
                repository,
                Decode,
                BackfillInventoryLoader.LoadForDigestion);
            CurrentRaw = loaded.Raw;
            Current = loaded.Snapshot;
            Document = loaded.Document;
        }

        internal RawRepositorySnapshot CurrentRaw { get; private set; }
        internal RepositorySnapshot Current { get; private set; }
        internal BackfillInventoryDocument Document { get; private set; }

        internal void Extend(IRepositoryGateway repository, params string[] paths)
        {
            var loaded = DigestionWorkingTree.Extend(
                repository,
                (CurrentRaw, Current, Document),
                Decode,
                paths);
            CurrentRaw = loaded.Raw;
            Current = loaded.Snapshot;
            Document = loaded.Document;
        }

        internal void ReadChainEvaluation(IRepositoryGateway repository, DigestionLedgerEntry target)
        {
            var closure = ChainClosureIds(Document, target.AtomId);
            var paths = Document.RequireDigestionEntries()
                .Where(entry => closure.Contains(entry.AtomId))
                .SelectMany(static entry => entry.CoverageGids
                    .Select(static gid => Gid.TryParse(gid, out var parsed) ? parsed.Path.Value : null)
                    .Append(entry.Receipts.TailAuthorization?.Path)
                    .Append(entry.SourcePath))
                .OfType<string>()
                .Concat(["D5", "Reg", "Trureturing.lean", "Golden/Frozen/state"])
                .Distinct(StringComparer.Ordinal)
                .ToArray();
            var loaded = DigestionWorkingTree.Extend(
                repository,
                (CurrentRaw, Current, Document),
                Decode,
                paths);
            CurrentRaw = loaded.Raw;
            Current = loaded.Snapshot;
            Document = loaded.Document;
        }

        internal void Commit(ImmutableArray<IngestCommand.LedgerUpdate> updates)
        {
            var entries = CurrentRaw.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
            foreach (var update in updates)
            {
                if (update.Bytes is { } bytes)
                    entries[update.Path] = new RawRepositoryEntry(update.Path, bytes);
                else
                    entries.Remove(update.Path);
            }

            CurrentRaw = RawRepositorySnapshot.Create(entries.Values);
            Current = Decode(CurrentRaw);
            Document = BackfillInventoryLoader.LoadForDigestion(Current);
        }
    }

    internal static CommandResult Run(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments,
        ILeanReportSource? reportSource = null) =>
        Run(root, repository, arguments, BackfillInventoryWriter.WriteAtom, ReadRequest,
            static (directory, current, updates) => IngestCommand.ApplyLedgerUpdatesAtomically(directory, current, updates), reportSource);

    internal static CommandResult Run(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments,
        Func<DigestionLedgerEntry, ImmutableArray<byte>> writeAtom,
        Func<string, string, ImmutableArray<byte>> readRequest,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>> applyUpdates,
        ILeanReportSource? reportSource = null)
        => RunCore(root, repository, arguments, writeAtom, readRequest, applyUpdates, reportSource,
            session: null, suppliedRequest: null);

    private static CommandResult RunCore(string root, IRepositoryGateway repository,
        IReadOnlyList<string> arguments,
        Func<DigestionLedgerEntry, ImmutableArray<byte>> writeAtom,
        Func<string, string, ImmutableArray<byte>> readRequest,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>> applyUpdates,
        ILeanReportSource? reportSource,
        Session? session,
        SettleRequest? suppliedRequest)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(root);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(writeAtom);
        ArgumentNullException.ThrowIfNull(readRequest);
        ArgumentNullException.ThrowIfNull(applyUpdates);
        try
        {
            var options = suppliedRequest is null ? ParseArguments(arguments) : null;
            var request = suppliedRequest
                ?? (options!.RequestPath is null ? null : LoadRequest(readRequest(root, options.RequestPath)));
            var atomId = request?.AtomId ?? options!.ClearAtomId!;
            session ??= new Session(repository);
            var current = session.CurrentRaw;
            var snapshot = session.Current;
            var document = session.Document;
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
                RequireWritable(target);
                var sourceCasPaths = DigestionWorkingTree.ChainCasPaths(
                    document,
                    [
                        target.AtomId,
                        .. document.RequireDigestionEntries()
                        .Where(entry => entry.SourceId == target.SourceId)
                        .SelectMany(static entry => entry.Receipts.ChainAtoms),
                    ]);
                var requiredPaths = new[]
                {
                    target.SourcePath,
                    TheoryAtomizerDataLoader.DataPath,
                }.Concat(sourceCasPaths).ToArray();
                session.Extend(repository, requiredPaths);
                current = session.CurrentRaw;
                snapshot = session.Current;
                document = session.Document;
                target = LocateTarget(document, atomId);
                var contexts = DigestionAtomContextProjection.ResolveOccurrences(snapshot, document, atomId);
                if (contexts.Length > 1 && request.OccurrenceIndex is null)
                    throw Invalid("OCCURRENCE_INDEX_REQUIRED", $"atom_id={atomId} occurrences={contexts.Length}");
                if (contexts.Length == 1 && request.OccurrenceIndex is not null)
                    throw Invalid("REQUEST_KEYS_INVALID", "occurrence_index is only valid for repeated occurrences");
                if (request.OccurrenceIndex is { } selected && (selected < 1 || selected > contexts.Length))
                    throw Invalid("OCCURRENCE_INDEX_INVALID", $"atom_id={atomId} occurrence_index={selected} occurrences={contexts.Length}");
                var context = contexts[request.OccurrenceIndex is { } occurrence ? occurrence - 1 : 0];
                if (context.Previous?.AtomId != request.PreviousAtomId || context.Next?.AtomId != request.NextAtomId)
                    throw Invalid("CONTEXT_MISMATCH", $"atom_id={atomId}");
                if (!target.Receipts.ChainAtoms.IsEmpty)
                {
                    session.ReadChainEvaluation(repository, target);
                    current = session.CurrentRaw;
                    snapshot = session.Current;
                    document = session.Document;
                    target = LocateTarget(document, atomId);
                    RequireCompleteChain(snapshot, document, target, reportSource);
                }
                updated = target with
                {
                    Receipts = target.Receipts with { Nonpropositional = new(request.Justification, request.PreviousAtomId, request.NextAtomId) },
                    ProjectedStatus = new(DigestionMigrationState.Nonpropositional, DigestionTruthState.Inapplicable),
                };
            }
            var (path, updates) = Write(root, current, target, updated, writeAtom, applyUpdates);
            session.Commit(updates);
            var sentinel = request is null ? "SETTLE_CLEARED" : "SETTLED_NONPROPOSITIONAL";
            var output = $"{sentinel} atom_id={atomId} path={path}\n";
            return new CommandResult(true, output, string.Empty);
        }
        catch (DigestionAtomContextException error)
        {
            return new CommandResult(false, string.Empty, $"SETTLE_INVALID {error.Code} {error.Message}\n");
        }
        catch (SettleAtomException error)
        {
            return new CommandResult(false, string.Empty, $"SETTLE_INVALID {error.Code} {error.Message}\n");
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"SETTLE_INVALID INFRASTRUCTURE {error.Message}\n");
        }
    }

    private static void RequireCompleteChain(RepositorySnapshot snapshot, BackfillInventoryDocument document,
        DigestionLedgerEntry target, ILeanReportSource? reportSource)
    {
        var entries = document.RequireDigestionEntries().GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .Where(static group => group.Count() == 1)
            .ToDictionary(static group => group.Key, static group => group.Single(), StringComparer.Ordinal);
        // Reuse decomposition's complete CAS/identity/Plan/Materialize validation, including
        // the target, before trusting any stored terminal directory or invoking the writer.
        var closure = DigestionDecomposition.ValidatedClosure([target.AtomId], entries, snapshot,
            TheoryAtomizerDataLoader.Load(snapshot));
        closure.Remove(target.AtomId);
        var closureDocument = ClosureDocument(document, closure, target.AtomId);
        DigestionLedgerEvaluation evaluation;
        if (closure.Any(id => !entries[id].Coverage.IsEmpty))
        {
            if (reportSource is null) throw Invalid("CHAIN_INCOMPLETE", "covered descendants require a current Lean report");
            var lean = LeanClosureValidator.Validate(snapshot, reportSource.Load(snapshot)) switch
            {
                LeanValidationOutcome.Accepted accepted => accepted.Capability,
                LeanValidationOutcome.InfrastructureFailure failure => throw Invalid("CHAIN_INCOMPLETE", failure.Message),
            };
            evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
                closureDocument, snapshot, lean, validateProjectedStatus: false);
        }
        else
        {
            // This complete descendant closure has no coverage edges to validate. Keep
            // unrelated managed Lean inputs outside the report-free receipt evaluation.
            evaluation = DigestionStatusEvaluator.EvaluateUncovered(DigestionEvaluationScope.FullScan,
                closureDocument, snapshot);
        }
        var evaluated = evaluation.Entries.ToDictionary(static item => item.Entry.AtomId, StringComparer.Ordinal);
        var streams = new Dictionary<string, DigestionAtomContextProjection.SourceStream>(StringComparer.Ordinal);
        foreach (var id in closure.Order(StringComparer.Ordinal))
        {
            if (!evaluated.TryGetValue(id, out var item) || item.DerivedStatus != item.Entry.ProjectedStatus
                || item.DerivedStatus.Migration is not (DigestionMigrationState.Absorbed or DigestionMigrationState.Nonpropositional)
                || item.DerivedStatus.Truth is DigestionTruthState.Open
                || !item.Gaps.IsEmpty || item.Entry.Receipts.Quarantine is not null
                || item.Entry.Receipts.CoverDisposition is not null)
                throw Invalid("CHAIN_INCOMPLETE", $"atom_id={target.AtomId} descendant={id}");
            if (item.Entry.Receipts.Nonpropositional is { } receipt)
            {
                if (!streams.TryGetValue(item.Entry.SourceId, out var stream))
                {
                    stream = DigestionAtomContextProjection.MaterializeSource(snapshot, document, item.Entry.SourceId);
                    streams.Add(item.Entry.SourceId, stream);
                }
                if (!stream.ResolveOccurrences(id).Any(context =>
                        context.Previous?.AtomId == receipt.PreviousAtomId && context.Next?.AtomId == receipt.NextAtomId))
                    throw Invalid("CONTEXT_MISMATCH", $"atom_id={target.AtomId} descendant={id}");
            }
        }
    }

    private static BackfillInventoryDocument ClosureDocument(
        BackfillInventoryDocument document,
        IReadOnlySet<string> descendants,
        string targetId) =>
        document.WithDigestionSources(document.RequireDigestionSources()
            .Select(source => source with
            {
                Entries = source.Entries
                    .Where(entry => entry.AtomId == targetId || descendants.Contains(entry.AtomId))
                    .ToImmutableArray(),
            })
            .Where(static source => !source.Entries.IsEmpty)
            .ToImmutableArray());

    private static HashSet<string> ChainClosureIds(BackfillInventoryDocument document, string root)
    {
        var entries = document.RequireDigestionEntries()
            .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .Where(static group => group.Count() == 1)
            .ToDictionary(static group => group.Key, static group => group.Single(), StringComparer.Ordinal);
        var closure = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Queue<string>();
        pending.Enqueue(root);
        while (pending.TryDequeue(out var id))
        {
            if (!closure.Add(id) || !entries.TryGetValue(id, out var entry)) continue;
            foreach (var child in entry.Receipts.ChainAtoms) pending.Enqueue(child);
        }

        return closure;
    }

    private static void RequireWritable(DigestionLedgerEntry entry)
    {
        if (entry.Receipts.Nonpropositional is not null
            || entry.ProjectedStatus != new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open))
            throw Invalid("NOT_RESIDUAL_OPEN", $"atom_id={entry.AtomId}");
        if (!entry.Coverage.IsEmpty) throw Invalid("COVERAGE_PRESENT", $"atom_id={entry.AtomId}");
        if (entry.Receipts.Quarantine is not null) throw Invalid("QUARANTINE_PRESENT", $"atom_id={entry.AtomId}");
        if (entry.Receipts.CoverDisposition is not null) throw Invalid("COVER_DISPOSITION_PRESENT", $"atom_id={entry.AtomId}");
        if (!entry.Receipts.UnresolvedSubitems.IsEmpty) throw Invalid("UNRESOLVED_SUBITEMS_PRESENT", $"atom_id={entry.AtomId}");
    }

    private static (string Path, ImmutableArray<IngestCommand.LedgerUpdate> Updates) Write(
        string root, RawRepositorySnapshot current, DigestionLedgerEntry original,
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
            var replay = LocateTarget(BackfillInventoryLoader.LoadForDigestion(Decode(final)), updated.AtomId);
            if (!writeAtom(replay).AsSpan().SequenceEqual(bytes.AsSpan()))
                throw new FormatException("serialized shard did not replay byte-identically");
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            throw Invalid("ROUND_TRIP_FAILED", $"atom_id={updated.AtomId} {error.Message}");
        }
        var updates = IngestCommand.LedgerUpdates(current, final);
        applyUpdates(root, current, updates);
        return (newPath, updates);
    }

    private static SettleRequest LoadRequest(ImmutableArray<byte> bytes)
    {
        var text = DecodeRequest(bytes);
        TomlTable table;
        try { table = TomlSerializer.Deserialize<TomlTable>(text) ?? throw new FormatException("request is empty"); }
        catch (Exception error) when (error is not OutOfMemoryException) { throw Invalid("REQUEST_TOML_INVALID", error.Message); }
        var keys = table.Keys.ToHashSet(StringComparer.Ordinal);
        var requiredKeys = new HashSet<string>(["atom_id", "justification", "previous_atom_id", "next_atom_id"], StringComparer.Ordinal);
        if (!keys.IsSupersetOf(requiredKeys) || keys.Any(key => !requiredKeys.Contains(key) && key != "occurrence_index"))
            throw Invalid("REQUEST_KEYS_INVALID", "request keys are not canonical");
        var atomId = RequiredString(table, "atom_id");
        if (!DigestionNonpropositional.IsAtomId(atomId)) throw Invalid("ARGUMENTS_INVALID", "atom_id must be a canonical atom id");
        int? occurrenceIndex = null;
        if (table.TryGetValue("occurrence_index", out var occurrenceValue))
        {
            if (occurrenceValue is not long raw || raw < 1 || raw > int.MaxValue)
                throw Invalid("OCCURRENCE_INDEX_INVALID", "occurrence_index must be a positive integer");
            occurrenceIndex = (int)raw;
        }
        return new SettleRequest(atomId, RequiredString(table, "justification"),
            Neighbor(table, "previous_atom_id"), Neighbor(table, "next_atom_id"), occurrenceIndex);
    }

    private static string DecodeRequest(ImmutableArray<byte> bytes)
    {
        if (bytes.IsEmpty || bytes[^1] != (byte)'\n' || bytes.AsSpan().Contains((byte)'\r')
            || bytes.AsSpan().StartsWith(Encoding.UTF8.Preamble))
            throw Invalid("REQUEST_ENCODING_INVALID", "request must be strict UTF-8 without BOM/CR and end in LF");
        string text;
        try { text = StrictUtf8.GetString(bytes.AsSpan()); }
        catch (DecoderFallbackException error) { throw Invalid("REQUEST_ENCODING_INVALID", error.Message); }
        return text;
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

    private static SettleAtomException Invalid(string code, string detail) => new(code, detail);

    private sealed class SettleAtomException(string code, string detail) : Exception(detail)
    {
        internal string Code { get; } = code;
    }

    private static SettleOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        string? request = null, clear = null;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--request" when request is null && index + 1 < arguments.Count: request = arguments[++index]; break;
                case "--clear" when clear is null && index + 1 < arguments.Count: clear = arguments[++index]; break;
                default: throw Invalid("ARGUMENTS_INVALID", Usage);
            }
        }
        if ((request is null) == (clear is null)
            || (clear is not null && !DigestionNonpropositional.IsAtomId(clear)))
            throw Invalid("ARGUMENTS_INVALID", Usage);
        return new SettleOptions(request, clear);
    }

    private sealed record SettleOptions(string? RequestPath, string? ClearAtomId);
    private sealed record SettleRequest(string AtomId, string Justification, string? PreviousAtomId, string? NextAtomId,
        int? OccurrenceIndex);
}
