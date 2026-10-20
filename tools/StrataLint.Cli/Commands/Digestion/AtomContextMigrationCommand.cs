using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class AtomContextMigrationCommand
{
    // Explicit writer scope: current source evidence, registered identities and their
    // actual chains. No ingest, status projection or coverage changes occur here.
    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadSource(
        IRepositoryGateway repository, string sourceId, RawRepositorySnapshot? overlay = null)
    {
        var raw = repository.ReadCurrent([DigestionQuerySelection.Literal(BackfillInventoryLoader.RootPath + sourceId),
            DigestionQuerySelection.Literal(FileMapLoader.RelativePath), ":(glob)Meta/FILEMAP.*.toml"]);
        if (overlay is not null)
        {
            var files = raw.Entries.ToDictionary(entry => entry.Path, StringComparer.Ordinal);
            foreach (var entry in overlay.Entries) files[entry.Path] = entry;
            raw = RawRepositorySnapshot.Create(files.Values);
        }
        var loaded = DigestionQuerySelection.Load(raw);
        var source = loaded.Document.RequireDigestionSources().Single(source => source.SourceId == sourceId);
        raw = DigestionQuerySelection.Merge(raw, repository.ReadCurrent([
            DigestionQuerySelection.Literal(source.SourcePath),
            .. loaded.Document.RequireDigestionEntries().Select(DigestionQuerySelection.CasPath)]));
        return DigestionQuerySelection.ReadChains(repository, DigestionQuerySelection.Load(raw));
    }

    internal static CommandResult Run(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments,
        Action<string, RawRepositorySnapshot, ImmutableArray<DigestionCasObject>, ImmutableArray<IngestCommand.LedgerUpdate>>? apply = null)
    {
        try
        {
            var selectors = new List<string>();
            var write = false;
            var all = false;
            for (var i = 0; i < arguments.Count; i++)
                switch (arguments[i])
                {
                    case "--source" when i + 1 < arguments.Count: selectors.Add(arguments[++i]); break;
                    case "--all" when !all: all = true; break;
                    case "--write" when !write: write = true; break;
                    default: throw new FormatException("USAGE: migrate-atom-context (--all | --source SOURCE ...) [--write]");
                }
            if (all == (selectors.Count > 0)) throw new FormatException("select --all or --source");
            var ids = all ? repository.SearchCurrentPaths([$":(glob){BackfillInventoryLoader.RootPath}*/source.toml"])
                .Select(DigestionQuerySelection.SourceId).Order(StringComparer.Ordinal).ToArray()
                : DigestionQuerySelection.ResolveSources(repository, selectors);
            var output = new System.Text.StringBuilder();
            var unresolvedAtoms = 0;
            var failedSources = 0;
            foreach (var sourceId in ids)
            {
                try
                {
                    var loaded = ReadSource(repository, sourceId);
                    var built = DigestionContextIndexBuilder.Build(loaded.Snapshot, loaded.Document, sourceId);
                    var final = DigestionContextPointerStore.Add(loaded.Raw, built.Index);
                    var before = loaded.Raw.Entries.ToDictionary(entry => entry.Path, StringComparer.Ordinal);
                    var updates = final.Entries.Where(entry => !before.TryGetValue(entry.Path, out var old)
                            || !old.Bytes.AsSpan().SequenceEqual(entry.Bytes.AsSpan()))
                        .Select(entry => new IngestCommand.LedgerUpdate(entry.Path, entry.Bytes)).ToImmutableArray();
                    var resolved = built.Index.Entries.Select(entry => entry.AtomId).ToHashSet(StringComparer.Ordinal);
                    var missing = loaded.Document.RequireDigestionEntries().Where(entry => entry.SourceId == sourceId
                        && !resolved.Contains(entry.AtomId)).Select(entry => entry.AtomId).Order(StringComparer.Ordinal).ToArray();
                    unresolvedAtoms += missing.Length;
                    if (write) (apply ?? IngestCommand.ApplyDecompositionAtomically)(root, loaded.Raw, built.CasObjects, updates);
                    output.AppendLine($"ATOM_CONTEXT_MIGRATION source_id={sourceId} version={built.Index.SourceSha256} resolved={resolved.Count} unresolved={missing.Length} changed={updates.Length} write={write.ToString().ToLowerInvariant()}");
                    foreach (var id in missing) output.AppendLine($"ATOM_CONTEXT_UNRESOLVED source_id={sourceId} atom_id={id} reason=no-supported-occurrence-in-observed-version");
                }
                catch (Exception error) when (error is not OutOfMemoryException)
                {
                    failedSources++;
                    output.AppendLine($"ATOM_CONTEXT_UNRESOLVED source_id={sourceId} reason={error.Message}");
                }
            }
            var complete = unresolvedAtoms == 0 && failedSources == 0;
            return new(complete, output.ToString(), complete ? string.Empty
                : $"ATOM_CONTEXT_MIGRATION_INCOMPLETE unresolved_atoms={unresolvedAtoms} failed_sources={failedSources}\n");
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            return new(false, string.Empty, $"ATOM_CONTEXT_MIGRATION_INVALID {error.Message}\n");
        }
    }
}
