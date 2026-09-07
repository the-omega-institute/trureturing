using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class StripScribeReceiptsCommand
{
    private const string Usage =
        "USAGE: StrataLint strip-scribe-receipts [--source SOURCE_ID]... [--dry-run]";

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments) =>
        Run(repositoryRoot, repository, arguments,
            static (root, current, updates) =>
                IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates));

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>> applyUpdates)
    {
        try
        {
            var options = Parse(arguments);
            var current = repository.ReadCurrent();
            var document = BackfillInventoryLoader.Load(Decode(current));
            if (document.RequireDigestionEntries().IsEmpty)
                throw new InvalidOperationException("digestion ledger contains no atom entries");
            var plan = Plan(document, options.SourceIds);
            var selected = plan.Changes.Select(static change => (change.SourceId, change.AtomId)).ToHashSet();
            var replacements = plan.Document.RequireDigestionEntries()
                .Where(entry => selected.Contains((entry.SourceId, entry.AtomId)))
                .ToDictionary(
                    static entry => $"{BackfillInventoryLoader.RootPath}{entry.SourceId}/"
                        + $"{DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)}-"
                        + $"{DigestionStatusNames.Truth(entry.ProjectedStatus.Truth)}/{entry.AtomId}.yaml",
                    BackfillInventoryWriter.WriteAtom,
                    StringComparer.Ordinal);
            // Rewriting both versions now omits Scribe, so select writes from the strip plan.
            var replacement = RawRepositorySnapshot.Create(current.Entries.Select(entry =>
                replacements.TryGetValue(entry.Path, out var bytes)
                    ? new RawRepositoryEntry(entry.Path, bytes)
                    : entry));
            var updates = IngestCommand.LedgerUpdates(current, replacement);
            if (!options.DryRun)
                applyUpdates(repositoryRoot, current, updates);
            return new CommandResult(true, Render(plan, options.DryRun), string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"SCRIBE_STRIP_INVALID {OneLineReason(exception)}\n");
        }
    }

    internal static StripPlan Plan(
        BackfillInventoryDocument document,
        ImmutableArray<string> sourceIds)
    {
        var duplicate = sourceIds.GroupBy(static sourceId => sourceId, StringComparer.Ordinal)
            .Where(static group => group.Count() > 1)
            .Select(static group => group.Key)
            .Order(StringComparer.Ordinal)
            .FirstOrDefault();
        if (duplicate is not null)
            throw new InvalidOperationException("duplicate source: " + duplicate);
        var selected = sourceIds.ToHashSet(StringComparer.Ordinal);
        var known = document.RequireDigestionSources()
            .Select(static source => source.SourceId)
            .ToHashSet(StringComparer.Ordinal);
        var unknown = selected.Except(known, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (unknown.Length > 0)
            throw new InvalidOperationException("unknown source: " + string.Join(", ", unknown));
        var changes = ImmutableArray.CreateBuilder<StripChange>();
        var replacement = document.WithDigestionSources(document.RequireDigestionSources()
            .Select(source => source with
            {
                Entries = source.Entries.Select(entry =>
                {
                    if ((selected.Count != 0 && !selected.Contains(source.SourceId))
                        || entry.Receipts.Scribe.IsEmpty)
                    {
                        return entry;
                    }

                    changes.Add(new StripChange(source.SourceId, entry.AtomId, entry.Receipts.Scribe.Length));
                    return entry with
                    {
                        Receipts = entry.Receipts with { Scribe = [] },
                    };
                }).ToImmutableArray(),
            }).ToImmutableArray());
        return new StripPlan(replacement, changes.ToImmutable());
    }

    private static StripOptions Parse(IReadOnlyList<string> arguments)
    {
        var sources = ImmutableArray.CreateBuilder<string>();
        var dryRun = false;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--source": sources.Add(Value()); break;
                case "--dry-run" when !dryRun: dryRun = true; break;
                default: throw new InvalidOperationException(Usage);
            }

            string Value()
            {
                if (++index >= arguments.Count || string.IsNullOrWhiteSpace(arguments[index])
                    || arguments[index] != arguments[index].Trim()
                    || arguments[index].StartsWith("--", StringComparison.Ordinal))
                {
                    throw new InvalidOperationException(Usage);
                }

                return arguments[index];
            }
        }

        return new StripOptions(sources.ToImmutable(), dryRun);
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidOperationException(failure.Message),
    };

    private static string OneLineReason(Exception exception)
    {
        var lines = exception.Message.Split(
            ['\r', '\n'],
            StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
        return lines.Length == 0 ? exception.GetType().Name : string.Join(' ', lines);
    }

    private static string Render(StripPlan plan, bool dryRun)
    {
        var changes = plan.Changes
            .OrderBy(static change => change.SourceId, StringComparer.Ordinal)
            .ThenBy(static change => change.AtomId, StringComparer.Ordinal)
            .ToArray();
        return string.Concat(changes.Select(change =>
                $"SCRIBE_STRIP source={change.SourceId} atom={change.AtomId} receipts={change.ReceiptCount}\n"))
            + $"SCRIBE_STRIP_SUMMARY entries={changes.Length} receipts={changes.Sum(static change => change.ReceiptCount)} "
            + $"dry_run={dryRun.ToString().ToLowerInvariant()}\n";
    }

    private sealed record StripOptions(
        ImmutableArray<string> SourceIds,
        bool DryRun);

    internal sealed record StripChange(string SourceId, string AtomId, int ReceiptCount);

    internal sealed record StripPlan(
        BackfillInventoryDocument Document,
        ImmutableArray<StripChange> Changes);
}
