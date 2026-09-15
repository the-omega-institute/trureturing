using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Cli;

internal static class SettleUpstreamCommand
{
    private const string Usage = "settle-upstream --request FILE --base REV | settle-upstream --clear ATOM_ID --base REV";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static CommandResult Run(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments) =>
        Run(root, repository, arguments, BackfillInventoryWriter.WriteAtom,
            (directory, path) => [.. File.ReadAllBytes(Path.GetFullPath(Path.Combine(directory, path)))],
            (directory, current, updates) => IngestCommand.ApplyLedgerUpdatesAtomically(directory, current, updates),
            UpstreamProbeVerifier.Production);

    internal static CommandResult Run(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments,
        Func<DigestionLedgerEntry, ImmutableArray<byte>> writer,
        Func<string, string, ImmutableArray<byte>> readRequest,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>> apply,
        Func<UpstreamProbeVerifier> verifier)
    {
        try
        {
            var options = ParseArguments(arguments);
            var request = options.Request is null ? null : LoadRequest(readRequest(root, options.Request));
            var atomId = request?.AtomId ?? options.Clear!;
            var current = repository.ReadCurrent();
            _ = repository.ReadRevision(options.Base);
            var snapshot = Decode(current);
            var document = BackfillInventoryLoader.Load(snapshot);
            var target = Locate(document, atomId);
            if (!target.Receipts.ChainAtoms.IsEmpty) throw Invalid("CHAIN_PARENT", $"atom_id={atomId}");
            var probePath = DigestionStatusEvaluator.UpstreamProbePath(target);
            DigestionLedgerEntry updated;
            byte[]? probe = null;
            if (request is null)
            {
                if (target.Receipts.Upstream is null) throw Invalid("UPSTREAM_ABSENT", $"atom_id={atomId}");
                updated = target with
                {
                    Receipts = target.Receipts with { Upstream = null },
                    ProjectedStatus = new(DigestionMigrationState.Residual, DigestionTruthState.Open),
                };
            }
            else
            {
                RequireWritable(target);
                var contexts = DigestionAtomContextProjection.ResolveOccurrences(snapshot, document, atomId);
                // The upstream request has exactly six keys and cannot select an occurrence.
                if (contexts.Length != 1) throw Invalid("OCCURRENCE_INDEX_REQUIRED", $"atom_id={atomId} occurrences={contexts.Length}");
                var context = contexts[0];
                if (context.Previous?.AtomId != request.Previous || context.Next?.AtomId != request.Next)
                    throw Invalid("CONTEXT_MISMATCH", $"atom_id={atomId}");
                probe = ReadProbe(root, request.Probe);
                if (!snapshot.TryGetFile("lake-manifest.json", out var manifest))
                    throw new FormatException("immutable revision is missing lake-manifest.json.");
                var axioms = verifier().Verify(root, probe, manifest.Text, request.Declarations);
                var receipt = new DigestionUpstream(request.Justification, request.Declarations,
                    MathlibManifest.Revision(snapshot), DigestionFingerprint.Compute(probe).RawSha256,
                    axioms, request.Previous, request.Next);
                if (receipt.ValidationError is { } invalid) throw new FormatException(invalid);
                if (target.Receipts.Upstream is { } existing && !SameReceipt(existing, receipt))
                    throw Invalid("UPSTREAM_CONFLICT", $"atom_id={atomId}");
                var oldProbe = current.Entries.SingleOrDefault(entry => entry.Path == probePath);
                if (oldProbe is not null && !oldProbe.Bytes.AsSpan().SequenceEqual(probe))
                    throw Invalid("UPSTREAM_CONFLICT", $"atom_id={atomId} canonical probe differs");
                updated = target with
                {
                    Receipts = target.Receipts with { Upstream = receipt },
                    ProjectedStatus = new(DigestionMigrationState.Upstream, DigestionTruthState.Closed),
                };
            }
            // Both creation and deletion participate in the ledger transaction and its rollback.
            UpstreamProbeVerifier.RequireNoLinks(root, Path.Combine(root, probePath));
            Write(root, current, target, updated, probePath, probe, writer, apply);
            var output = request is null
                ? $"SETTLE_UPSTREAM_CLEARED atom_id={atomId} state=residual-open probe={probePath}\n"
                : $"SETTLE_UPSTREAM atom_id={atomId} state=upstream-closed probe={probePath} declarations={request.Declarations.Length} axioms=[{string.Join(',', updated.Receipts.Upstream!.ProbeAxioms)}] mathlib_rev={updated.Receipts.Upstream.MathlibRev}\n";
            var ancestors = SettleAtomCommand.CoveredAncestors(document, atomId);
            if (ancestors.Length > 0) output += "SETTLE_ALIGN_REQUIRED ancestors=" + string.Join(',', ancestors) + "\n";
            return new(true, output, string.Empty);
        }
        catch (DigestionAtomContextException error) { return Failure(error.Code.ToString(), error.Message); }
        catch (UpstreamSettlementException error) { return Failure(error.Code, error.Message); }
        catch (Exception error) when (error is not OutOfMemoryException) { return Failure("INFRASTRUCTURE", error.Message); }
    }

    private static void RequireWritable(DigestionLedgerEntry entry)
    {
        var expected = entry.Receipts.Upstream is null
            ? new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open)
            : new DigestionStatus(DigestionMigrationState.Upstream, DigestionTruthState.Closed);
        if (entry.ProjectedStatus != expected) throw Invalid("NOT_RESIDUAL_OPEN", $"atom_id={entry.AtomId}");
        if (!entry.Coverage.IsEmpty) throw Invalid("COVERAGE_PRESENT", $"atom_id={entry.AtomId}");
        if (entry.Receipts.Quarantine is not null) throw Invalid("QUARANTINE_PRESENT", $"atom_id={entry.AtomId}");
        if (entry.Receipts.CoverDisposition is not null) throw Invalid("DISPOSITION_PRESENT", $"atom_id={entry.AtomId}");
        if (entry.Receipts.Nonpropositional is not null) throw Invalid("NONPROPOSITIONAL_PRESENT", $"atom_id={entry.AtomId}");
        if (!entry.Receipts.UnresolvedSubitems.IsEmpty) throw Invalid("UNRESOLVED_SUBITEMS_PRESENT", $"atom_id={entry.AtomId}");
    }

    private static void Write(string root, RawRepositorySnapshot current, DigestionLedgerEntry target,
        DigestionLedgerEntry updated, string probePath, byte[]? probe,
        Func<DigestionLedgerEntry, ImmutableArray<byte>> writer,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>> apply)
    {
        RawRepositorySnapshot final;
        try
        {
            var bytes = writer(updated);
            var entries = current.Entries.Where(entry => entry.Path != AtomPath(target) && entry.Path != probePath)
                .Append(new RawRepositoryEntry(AtomPath(updated), bytes));
            if (probe is not null) entries = entries.Append(new RawRepositoryEntry(probePath, [.. probe]));
            final = RawRepositorySnapshot.Create(entries);
            var replay = Locate(BackfillInventoryLoader.Load(Decode(final)), target.AtomId);
            if (!writer(replay).AsSpan().SequenceEqual(bytes.AsSpan())) throw new FormatException("serialized shard did not replay byte-identically");
            if (probe is not null && replay.Receipts.Upstream?.ProbeSha256 != DigestionFingerprint.Compute(probe).RawSha256)
                throw new FormatException("serialized probe hash does not match the written bytes");
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        { throw Invalid("ROUND_TRIP_FAILED", $"atom_id={target.AtomId} {error.Message}"); }
        var updates = IngestCommand.LedgerUpdates(current, final);
        var originalProbe = current.Entries.SingleOrDefault(entry => entry.Path == probePath);
        if (probe is null ? originalProbe is not null : originalProbe is null || !originalProbe.Bytes.AsSpan().SequenceEqual(probe))
            updates = updates.Add(new(probePath, probe is null ? null : [.. probe], probe is null ? int.MaxValue : int.MinValue));
        if (!updates.IsEmpty) apply(root, current, updates);
    }

    private static Request LoadRequest(ImmutableArray<byte> bytes)
    {
        if (bytes.IsEmpty || bytes[^1] != (byte)'\n' || bytes.AsSpan().Contains((byte)'\r') || bytes.AsSpan().StartsWith(Encoding.UTF8.Preamble))
            throw Invalid("REQUEST_ENCODING_INVALID", "request must be strict UTF-8 without BOM/CR and end in LF");
        string text;
        try { text = StrictUtf8.GetString(bytes.AsSpan()); }
        catch (DecoderFallbackException error) { throw Invalid("REQUEST_ENCODING_INVALID", error.Message); }
        TomlTable table;
        try { table = TomlSerializer.Deserialize<TomlTable>(text) ?? throw new FormatException("empty request"); }
        catch (Exception error) when (error is not OutOfMemoryException) { throw Invalid("REQUEST_KEYS_INVALID", error.Message); }
        if (!table.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(["atom_id", "justification", "declarations", "probe", "previous_atom_id", "next_atom_id"]))
            throw Invalid("REQUEST_KEYS_INVALID", "request keys are not canonical");
        var atomId = RequiredString(table, "atom_id");
        if (!DigestionNonpropositional.IsAtomId(atomId)) throw Invalid("ARGUMENTS_INVALID", "atom_id must be canonical");
        if (table["declarations"] is not TomlArray array || array.Count == 0
            || array.Any(value => value is not string name || !DigestionUpstream.IsDeclarationName(name)))
            throw Invalid("ARGUMENTS_INVALID", "declarations must be nonempty upstream declaration names");
        // Canonicalize order; duplicates are rejected, never silently deduplicated.
        var declarations = array.Cast<string>().Order(StringComparer.Ordinal).ToImmutableArray();
        if (declarations.Distinct(StringComparer.Ordinal).Count() != declarations.Length)
            throw Invalid("ARGUMENTS_INVALID", "declarations contain duplicates");
        return new(atomId, RequiredString(table, "justification"), declarations, RequiredString(table, "probe"),
            Neighbor(table, "previous_atom_id"), Neighbor(table, "next_atom_id"));
    }

    private static byte[] ReadProbe(string root, string requested)
    {
        try
        {
            var path = Path.GetFullPath(Path.Combine(root, requested));
            if (Path.IsPathRooted(requested) || !path.StartsWith(Path.TrimEndingDirectorySeparator(Path.GetFullPath(root)) + Path.DirectorySeparatorChar, StringComparison.Ordinal))
                throw Invalid("PROBE_PATH_INVALID", "probe must be relative to and inside the worktree");
            UpstreamProbeVerifier.RequireNoLinks(root, path);
            return File.ReadAllBytes(path);
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException or ArgumentException or NotSupportedException)
        { throw Invalid("PROBE_PATH_INVALID", error.Message); }
    }

    private static string RequiredString(TomlTable table, string key) => table[key] is string value && !string.IsNullOrWhiteSpace(value)
        && value == value.Trim() ? value : throw Invalid("ARGUMENTS_INVALID", $"{key} must be a nonblank unpadded string");
    private static string? Neighbor(TomlTable table, string key)
    {
        var value = RequiredString(table, key);
        if (value == "source-boundary") return null;
        return DigestionNonpropositional.IsAtomId(value) ? value : throw Invalid("ARGUMENTS_INVALID", $"{key} must be a canonical atom id or source-boundary");
    }
    private static (string? Request, string? Clear, string Base) ParseArguments(IReadOnlyList<string> arguments)
    {
        string? request = null, clear = null, baseline = null;
        for (var i = 0; i < arguments.Count; i++)
        {
            switch (arguments[i])
            {
                case "--request" when request is null && i + 1 < arguments.Count: request = arguments[++i]; break;
                case "--clear" when clear is null && i + 1 < arguments.Count: clear = arguments[++i]; break;
                case "--base" when baseline is null && i + 1 < arguments.Count: baseline = arguments[++i]; break;
                default: throw Invalid("ARGUMENTS_INVALID", Usage);
            }
        }
        if (string.IsNullOrWhiteSpace(baseline) || baseline != baseline.Trim() || (request is null) == (clear is null)
            || request is not null && (string.IsNullOrWhiteSpace(request) || request != request.Trim())
            || clear is not null && !DigestionNonpropositional.IsAtomId(clear)) throw Invalid("ARGUMENTS_INVALID", Usage);
        return (request, clear, baseline);
    }
    private static DigestionLedgerEntry Locate(BackfillInventoryDocument document, string atomId)
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
        + DigestionStatusNames.Migration(entry.ProjectedStatus.Migration) + "-" + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth) + "/" + entry.AtomId + ".yaml";
    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure error => throw new FormatException(error.Message),
    };
    private static bool SameReceipt(DigestionUpstream a, DigestionUpstream b) =>
        a.Justification == b.Justification && a.Declarations.SequenceEqual(b.Declarations) && a.MathlibRev == b.MathlibRev
        && a.ProbeSha256 == b.ProbeSha256 && a.ProbeAxioms.SequenceEqual(b.ProbeAxioms) && a.PreviousAtomId == b.PreviousAtomId && a.NextAtomId == b.NextAtomId;
    private static UpstreamSettlementException Invalid(string code, string detail) => new(code, detail);
    private static CommandResult Failure(string code, string detail) => new(false, string.Empty, $"SETTLE_UPSTREAM_INVALID {code} {detail}\n");
    private sealed record Request(string AtomId, string Justification, ImmutableArray<string> Declarations, string Probe, string? Previous, string? Next);
}
