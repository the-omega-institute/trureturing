using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class AtomContextMigrationCommand
{
    // Explicit writer scope: observed source evidence, registered identities and their
    // actual chains. No ingest, status projection or coverage changes occur here.
    internal static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document,
        DigestionContextPointerIndex? SavedIndex) ReadSource(
        IRepositoryGateway repository, string sourceId, RawRepositorySnapshot? overlay = null, string? sourceRevision = null,
        IReadOnlyList<string>? atomIds = null)
    {
        var sourceRoot = BackfillInventoryLoader.RootPath + sourceId + "/";
        var raw = repository.ReadCurrent([.. atomIds is { Count: > 0 }
                ? new[] { DigestionQuerySelection.Literal(sourceRoot + "source.toml"), DigestionQuerySelection.Literal(sourceRoot + "context") }
                : new[] { DigestionQuerySelection.Literal(sourceRoot.TrimEnd('/')) },
            DigestionQuerySelection.Literal(FileMapLoader.RelativePath), ":(glob)Meta/FILEMAP.*.toml"]);
        if (atomIds is { Count: > 0 })
        {
            var selected = DigestionQuerySelection.ReadAtoms(repository, atomIds, [sourceId]);
            var entries = selected.Document.RequireDigestionEntries();
            foreach (var id in atomIds)
                if (entries.Count(entry => entry.AtomId == id && entry.SourceId == sourceId) != 1)
                    throw new FormatException($"selected atom_id={id} is absent or ambiguous in source_id={sourceId}");
            raw = DigestionQuerySelection.Merge(raw, selected.Raw);
        }
        if (overlay is not null)
        {
            var files = raw.Entries.ToDictionary(entry => entry.Path, StringComparer.Ordinal);
            foreach (var entry in overlay.Entries) files[entry.Path] = entry;
            raw = RawRepositorySnapshot.Create(files.Values);
        }
        var loaded = DigestionQuerySelection.Load(raw);
        var source = loaded.Document.RequireDigestionSources().Single(source => source.SourceId == sourceId);
        raw = DigestionQuerySelection.Merge(raw, repository.ReadCurrent(
            loaded.Document.RequireDigestionEntries().Select(DigestionQuerySelection.CasPath).ToArray()));
        var sourceRaw = sourceRevision is null
            ? repository.ReadCurrent([DigestionQuerySelection.Literal(source.SourcePath)])
            : repository.ReadRevision(sourceRevision, [DigestionQuerySelection.Literal(source.SourcePath)]);
        // The immutable revision supplies only the observed prose. Current metadata,
        // identities, chains, coverage and FILEMAP retain their validation authority.
        raw = DigestionQuerySelection.Merge(raw, RawRepositorySnapshot.Create(sourceRaw.Entries
            .Where(entry => entry.Path == source.SourcePath)));
        if (atomIds is { Count: > 0 })
        {
            var observed = sourceRaw.Entries.Single(entry => entry.Path == source.SourcePath).Bytes;
            // Discover source roots by immutable bodies, before parsing accounts.
            // Selection must not collapse an omitted neighboring chain to its root,
            // while an account absent from this observation is not a dependency.
            var ownerIds = repository.SearchCurrentPaths([$":(glob){sourceRoot}*/*.yaml"])
                .Where(BackfillInventoryLoader.IsCanonicalPath).Select(Path.GetFileNameWithoutExtension)
                .OfType<string>().Distinct(StringComparer.Ordinal).ToArray();
            var bodies = repository.ReadCurrent(ownerIds.Select(id =>
                DigestionQuerySelection.Literal(DigestionCasStore.RootPath + id)).ToArray());
            var saved = TryUseSavedGraph(repository, raw, source, atomIds, observed, bodies);
            if (saved is { } reused) return reused;
            var observedIds = bodies.Entries.Where(body => !body.Bytes.IsEmpty
                    && observed.AsSpan().IndexOf(body.Bytes.AsSpan()) >= 0)
                .Select(body => Path.GetFileName(body.Path));
            var fresh = AtomizerRegistry.Require(source.Atomizer).Atomize(observed.AsSpan());
            var references = DigestionAtomContextProjection.SourceReferenceRootIds(fresh.Claims, observed,
                System.Text.Encoding.UTF8.GetString(observed.AsSpan()));
            references.UnionWith(observedIds);
            var referenced = DigestionQuerySelection.ReadAtoms(repository, references.ToArray());
            raw = DigestionQuerySelection.Merge(raw, referenced.Raw);
            loaded = DigestionQuerySelection.Load(raw);
            raw = DigestionQuerySelection.Merge(raw, repository.ReadCurrent(
                loaded.Document.RequireDigestionEntries().Select(DigestionQuerySelection.CasPath).ToArray()));
        }
        var complete = DigestionQuerySelection.ReadChains(repository, DigestionQuerySelection.Load(raw));
        return (complete.Raw, complete.Snapshot, complete.Document, null);
    }

    internal static CommandResult Run(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments,
        Action<string, RawRepositorySnapshot, ImmutableArray<DigestionCasObject>, ImmutableArray<IngestCommand.LedgerUpdate>>? apply = null)
    {
        try
        {
            var selectors = new List<string>();
            var atomIds = new List<string>();
            string? sourceRevision = null;
            var write = false;
            var all = false;
            for (var i = 0; i < arguments.Count; i++)
                switch (arguments[i])
                {
                    case "--source" when i + 1 < arguments.Count: selectors.Add(arguments[++i]); break;
                    case "--atom-id" when i + 1 < arguments.Count:
                        var atomId = arguments[++i];
                        if (!DigestionNonpropositional.IsAtomId(atomId)) throw new FormatException("invalid atom_id");
                        atomIds.Add(atomId);
                        break;
                    case "--source-revision" when sourceRevision is null && i + 1 < arguments.Count:
                        sourceRevision = arguments[++i];
                        if (sourceRevision.Length != 40 || sourceRevision.Any(character =>
                            character is not (>= '0' and <= '9') and not (>= 'a' and <= 'f')))
                            throw new FormatException("source revision must be an immutable 40-digit commit SHA");
                        break;
                    case "--all" when !all: all = true; break;
                    case "--write" when !write: write = true; break;
                    default: throw new FormatException("USAGE: migrate-atom-context (--all | --source SOURCE ...) [--atom-id ID ...] [--source-revision COMMIT_SHA] [--write]");
                }
            if (all == (selectors.Count > 0)) throw new FormatException("select --all or --source");
            var ids = all ? repository.SearchCurrentPaths([$":(glob){BackfillInventoryLoader.RootPath}*/source.toml"])
                .Select(DigestionQuerySelection.SourceId).Order(StringComparer.Ordinal).ToArray()
                : DigestionQuerySelection.ResolveSources(repository, selectors);
            if (atomIds.Count > 0 && (all || ids.Length != 1))
                throw new FormatException("--atom-id requires exactly one selected source");
            var output = new System.Text.StringBuilder();
            var unresolvedAtoms = 0;
            var failedSources = 0;
            foreach (var sourceId in ids)
            {
                try
                {
                    var loaded = ReadSource(repository, sourceId, sourceRevision: sourceRevision, atomIds: atomIds);
                    var built = loaded.SavedIndex is { } savedIndex ? new DigestionContextIndexBuild(savedIndex, [])
                        : DigestionContextIndexBuilder.Build(loaded.Snapshot, loaded.Document, sourceId);
                    built = built with { Index = DigestionContextPointerStore.PreserveSavedGraph(loaded.Raw, built.Index) };
                    var final = DigestionContextPointerStore.Add(loaded.Raw, built.Index);
                    var before = loaded.Raw.Entries.ToDictionary(entry => entry.Path, StringComparer.Ordinal);
                    var updates = final.Entries.Where(entry => !before.TryGetValue(entry.Path, out var old)
                            || !old.Bytes.AsSpan().SequenceEqual(entry.Bytes.AsSpan()))
                        .Select(entry => new IngestCommand.LedgerUpdate(entry.Path, entry.Bytes)).ToImmutableArray();
                    var saved = final.Entries.ToDictionary(entry => entry.Path, StringComparer.Ordinal);
                    var owners = loaded.Document.RequireDigestionEntries().Where(entry => entry.SourceId == sourceId
                        && (atomIds.Count == 0 || atomIds.Contains(entry.AtomId, StringComparer.Ordinal))).ToArray();
                    var missing = owners.Where(entry => !HasSaved(entry.AtomId))
                        .Select(entry => entry.AtomId).Order(StringComparer.Ordinal).ToArray();
                    var resolved = owners.Length - missing.Length;
                    bool HasSaved(string atomId) => saved.TryGetValue(
                        DigestionContextPointerIndex.RelativePath(sourceId, atomId), out var file)
                        && !DigestionContextPointerStore.ParseVersions(file.Bytes, sourceId, atomId).IsEmpty;
                    unresolvedAtoms += missing.Length;
                    if (write)
                    {
                        var expected = sourceRevision is null ? loaded.Raw : RawRepositorySnapshot.Create(
                            loaded.Raw.Entries.Where(entry => entry.Path != built.Index.SourcePath));
                        (apply ?? IngestCommand.ApplyDecompositionAtomically)(root, expected, built.CasObjects, updates);
                    }
                    output.AppendLine($"ATOM_CONTEXT_MIGRATION source_id={sourceId} version={built.Index.SourceSha256} resolved={resolved} unresolved={missing.Length} changed={updates.Length} write={write.ToString().ToLowerInvariant()}");
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
