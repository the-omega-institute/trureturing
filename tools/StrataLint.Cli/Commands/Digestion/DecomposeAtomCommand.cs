using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DecomposeAtomCommand
{
    internal static CommandResult Run(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments) =>
        Run(root, repository, arguments, IngestCommand.ApplyDecompositionAtomically);

    internal static CommandResult Run(string root, IRepositoryGateway repository,
        IReadOnlyList<string> arguments,
        Action<string, RawRepositorySnapshot, ImmutableArray<DigestionCasObject>, ImmutableArray<IngestCommand.LedgerUpdate>> apply,
        Func<string, TheoryAtomizer>? atomizerResolver = null)
    {
        try
        {
            var (id, revision, dryRun) = Parse(arguments);
            var raw = repository.ReadCurrent();
            _ = repository.ReadRevision(revision);
            var snapshot = Decode(raw);
            var ledger = BackfillInventoryLoader.Load(snapshot);
            var matches = ledger.RequireDigestionEntries().Where(entry => entry.AtomId == id).ToArray();
            if (matches.Length != 1) throw new FormatException($"ATOM_AMBIGUOUS atom_id={id} count={matches.Length}");
            var parent = matches[0];
            if (parent.Receipts.Quarantine is not null) throw new FormatException("QUARANTINED parent");
            if (!(parent.ProjectedStatus.Migration == DigestionMigrationState.Partial
                || parent.ProjectedStatus == new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open)))
                throw new FormatException("PARENT_STATE requires residual-open or partial parent");
            if (!snapshot.TryGetFile(DigestionCasStore.RootPath + id, out var blob))
                throw new FormatException($"CAS_MISSING atom_id={id}");
            var rules = TheoryAtomizerDataLoader.Load(snapshot);
            var atomizer = (atomizerResolver ?? (static name => AtomizerRegistry.Require(name).Atomize))(parent.Atomizer);
            var plan = DigestionDecomposition.Plan(parent, blob.RawBytes, atomizer, rules);
            var entries = ledger.RequireDigestionEntries().ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
            var writes = DigestionDecomposition.Materialize(parent, plan, entries);
            foreach (var child in plan.Children)
            {
                var childId = child.Fingerprints.RawSha256[7..];
                if (entries.ContainsKey(childId)
                    && (!snapshot.TryGetFile(DigestionCasStore.RootPath + childId, out var childBlob)
                        || !childBlob.RawBytes.AsSpan().SequenceEqual(child.RawBytes.AsSpan())))
                    throw new FormatException($"CHILD_CAS_MISMATCH atom_id={childId}");
            }

            var overlay = raw.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
            var updates = ImmutableArray.CreateBuilder<IngestCommand.LedgerUpdate>();
            foreach (var entry in writes.NewEntries.Append(writes.Parent))
            {
                var path = PathFor(entry);
                var bytes = BackfillInventoryWriter.WriteAtom(entry);
                if (overlay.TryGetValue(path, out var old) && old.Bytes.AsSpan().SequenceEqual(bytes.AsSpan())) continue;
                updates.Add(new IngestCommand.LedgerUpdate(path, bytes, entry.AtomId == id ? 1 : 0));
                overlay[path] = new RawRepositoryEntry(path, bytes);
            }
            foreach (var item in writes.CasObjects)
            {
                if (overlay.TryGetValue(item.RelativePath, out var old) && !old.Bytes.AsSpan().SequenceEqual(item.Bytes.AsSpan()))
                    throw new FormatException($"CAS_MISMATCH path={item.RelativePath}");
                overlay[item.RelativePath] = new RawRepositoryEntry(item.RelativePath, item.Bytes);
            }
            var final = RawRepositorySnapshot.Create(overlay.Values);
            var replayed = BackfillInventoryLoader.Load(Decode(final));
            foreach (var entry in writes.NewEntries.Append(writes.Parent))
            {
                var roundTrip = replayed.RequireDigestionEntries().Single(item => item.AtomId == entry.AtomId);
                if (!BackfillInventoryWriter.WriteAtom(roundTrip).AsSpan().SequenceEqual(overlay[PathFor(entry)].Bytes.AsSpan()))
                    throw new FormatException($"ROUND_TRIP_FAILED atom_id={entry.AtomId}");
            }
            var ledgerUpdates = updates.ToImmutable();
            var output = Render(id, plan, entries, writes.CasObjects, ledgerUpdates, dryRun);
            if (!dryRun && (!ledgerUpdates.IsEmpty || !writes.CasObjects.IsEmpty))
                apply(root, raw, writes.CasObjects, ledgerUpdates);
            return new CommandResult(true, output, string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"DECOMPOSE_INVALID {exception.Message}\n");
        }
    }

    private static string Render(string id, DigestionClausePlan plan,
        IReadOnlyDictionary<string, DigestionLedgerEntry> entries,
        ImmutableArray<DigestionCasObject> cas, ImmutableArray<IngestCommand.LedgerUpdate> updates, bool dryRun)
    {
        var output = new StringBuilder();
        foreach (var segment in plan.Segments)
        {
            var type = segment.Kind switch
            {
                DigestionSegmentKind.Claim => "claim",
                DigestionSegmentKind.Structural => "structural",
                _ => throw new FormatException("UNKNOWN_SEGMENT_KIND"),
            };
            var childId = segment.Kind == DigestionSegmentKind.Claim ? segment.Atom.Fingerprints.RawSha256[7..] : "-";
            output.AppendLine($"DECOMPOSE_SEGMENT type={type} child_id={childId} start={segment.Atom.StartByte} end={segment.Atom.EndByte} reused={entries.ContainsKey(childId).ToString().ToLowerInvariant()}");
        }
        foreach (var item in cas)
            output.AppendLine($"DECOMPOSE_WRITE path={item.RelativePath} sha256={item.Reference} bytes={item.Bytes.Length}");
        foreach (var item in updates)
            output.AppendLine($"DECOMPOSE_WRITE path={item.Path} sha256={DigestionCasStore.Capture(item.Bytes!.Value.AsSpan()).Reference} bytes={item.Bytes.Value.Length}");
        output.AppendLine($"DECOMPOSE_WRITTEN atom_id={id} children={plan.Children.Length} cas_objects={cas.Length} ledger_updates={updates.Length} dry_run={dryRun.ToString().ToLowerInvariant()}");
        return output.ToString();
    }

    private static string PathFor(DigestionLedgerEntry entry) =>
        $"{BackfillInventoryLoader.RootPath}{entry.SourceId}/"
        + $"{DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)}-"
        + $"{DigestionStatusNames.Truth(entry.ProjectedStatus.Truth)}/{entry.AtomId}.yaml";

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure failure => throw new FormatException(failure.Message),
    };

    private static (string AtomId, string BaseRevision, bool DryRun) Parse(IReadOnlyList<string> arguments)
    {
        string? atom = null;
        string? revision = null;
        var dryRun = false;
        var invalid = new FormatException("ARGUMENTS_INVALID USAGE: StrataLint decompose-atom --atom ATOM_ID --base REV [--dry-run]");
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--atom" when atom is null && index + 1 < arguments.Count: atom = arguments[++index]; break;
                case "--base" when revision is null && index + 1 < arguments.Count: revision = arguments[++index]; break;
                case "--dry-run" when !dryRun: dryRun = true; break;
                default: throw invalid;
            }
        }
        if (atom is null || !DigestionFingerprint.IsCanonicalSha256("sha256:" + atom)
            || string.IsNullOrWhiteSpace(revision) || revision != revision.Trim() || revision.StartsWith("--", StringComparison.Ordinal))
            throw invalid;
        return (atom, revision, dryRun);
    }
}
