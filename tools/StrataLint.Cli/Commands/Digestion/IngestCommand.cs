using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    // Brings the recorded ledger in line with what the current tree derives:
    // coverage targets are refreshed from the Lean report and the frozen state,
    // then every entry takes its derived status.
    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(arguments);
        if (arguments.Contains("--refresh-source", StringComparer.Ordinal))
        {
            return RefreshSourceRegistry(repositoryRoot, repository, arguments);
        }

        try
        {
            var planOnly = ParseArguments(arguments);
            var (currentRaw, current, document) = DigestionWorkingTree.Read(
                repository,
                Decode,
                static snapshot => LoadDocument(snapshot));
            var lean = ValidateLean(current, leanReportSource.Load(current));
            var truthStates = LeanTruthStates.Resolve(current, lean);
            var retargeted = DigestionCoverageTargetAligner.Align(document, current, lean, truthStates);
            var evaluation = DigestionStatusEvaluator.Evaluate(
                DigestionEvaluationScope.FullScan,
                retargeted,
                current,
                lean,
                validateProjectedStatus: false,
                truthStates: truthStates);
            RequireNoReceiptIntegrityFailure(evaluation);

            var derived = evaluation.Entries.ToDictionary(
                static item => (item.Entry.SourceId, item.Entry.AtomId),
                static item => item.DerivedStatus);
            var aligned = retargeted.WithDigestionSources(
                retargeted.RequireDigestionSources()
                    .Select(source => source with
                    {
                        Entries = source.Entries
                            .Select(entry => entry with
                            {
                                ProjectedStatus = derived[(entry.SourceId, entry.AtomId)],
                            })
                            .ToImmutableArray(),
                    })
                    .ToImmutableArray());
            var finalRaw = ReplaceLedger(currentRaw, document, aligned);
            var ledgerUpdates = LedgerUpdates(currentRaw, finalRaw, document, aligned);
            if (!planOnly)
            {
                ApplyLedgerUpdatesAtomically(repositoryRoot, currentRaw, ledgerUpdates);
            }

            return new CommandResult(
                true,
                RenderAlignment(document, aligned, ledgerUpdates.Length, applied: !planOnly),
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"ALIGN_INVALID {exception.Message}\n");
        }
    }

    private static bool ParseArguments(IReadOnlyList<string> arguments) => arguments.Count switch
    {
        0 => false,
        1 when arguments[0] == "--plan" => true,
        _ => throw new InvalidOperationException(
            "USAGE: StrataLint align-digestion-status [--plan] | --refresh-source EXISTING_ID_OR_PATH [--plan]"),
    };

    private static string RenderAlignment(
        BackfillInventoryDocument before,
        BackfillInventoryDocument after,
        int ledgerFilesChanged,
        bool applied)
    {
        var previous = before.RequireDigestionEntries().ToDictionary(
            static entry => (entry.SourceId, entry.AtomId));
        var changed = after.RequireDigestionEntries()
            .Select(entry => (Entry: entry, Previous: previous[(entry.SourceId, entry.AtomId)]))
            .Where(static item => item.Entry.ProjectedStatus != item.Previous.ProjectedStatus
                || !item.Entry.Coverage.SequenceEqual(item.Previous.Coverage))
            .OrderBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
            .ThenBy(static item => item.Entry.AtomId, StringComparer.Ordinal)
            .ToArray();
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        writer.Write(
            $"ALIGN entries={previous.Count} "
            + $"status_changed={changed.Count(static item => item.Entry.ProjectedStatus != item.Previous.ProjectedStatus)} "
            + $"coverage_retargeted={changed.Count(static item => !item.Entry.Coverage.SequenceEqual(item.Previous.Coverage))} "
            + $"ledger_files_changed={ledgerFilesChanged} "
            + $"applied={applied.ToString().ToLowerInvariant()}\n");
        foreach (var (entry, old) in changed)
        {
            writer.Write(
                $"ALIGN_ENTRY source={entry.SourceId} atom={entry.AtomId} "
                + $"from={StatusName(old.ProjectedStatus)} to={StatusName(entry.ProjectedStatus)}\n");
        }

        return writer.ToString();
    }

    private static string StatusName(DigestionStatus status) =>
        DigestionStatusNames.Migration(status.Migration) + "-" + DigestionStatusNames.Truth(status.Truth);

    internal static BackfillInventoryDocument LoadDocument(RepositorySnapshot snapshot) =>
        BackfillInventoryLoader.Load(snapshot);

    internal static RawRepositorySnapshot ReplaceLedger(
        RawRepositorySnapshot snapshot,
        BackfillInventoryDocument current,
        BackfillInventoryDocument replacement)
    {
        var matches = snapshot.Entries.Count(static entry =>
            entry.Path == BackfillInventoryLoader.RelativePath);
        if (matches > 0)
        {
            throw new InvalidOperationException("ingest does not write legacy digestion ledgers");
        }

        var entries = snapshot.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        var currentSources = current.RequireDigestionSources().ToDictionary(
            static source => source.SourceId,
            StringComparer.Ordinal);
        var replacementSources = replacement.RequireDigestionSources().ToDictionary(
            static source => source.SourceId,
            StringComparer.Ordinal);
        // Adding is how a theory document nobody declared enters the ledger, so it is
        // allowed and writes the source metadata below. The current writer does not
        // remove a source because that would also discard its receipts.
        var removed = currentSources.Keys.Except(replacementSources.Keys, StringComparer.Ordinal).ToArray();
        if (removed.Length > 0)
        {
            throw new InvalidOperationException(
                "ingest cannot remove directory ledger sources: "
                + string.Join(", ", removed.Order(StringComparer.Ordinal)));
        }

        foreach (var (sourceId, replacementSource) in replacementSources)
        {
            if (currentSources.TryGetValue(sourceId, out var currentSource)
                && SourceMetadataEquals(currentSource, replacementSource))
            {
                continue;
            }

            var metadataPath = $"{BackfillInventoryLoader.RootPath}{sourceId}/source.toml";
            entries[metadataPath] = new RawRepositoryEntry(
                metadataPath,
                BackfillInventoryWriter.WriteSourceMetadata(replacementSource));
        }

        var currentEntries = current.RequireDigestionEntries().ToDictionary(
            static entry => (entry.SourceId, entry.AtomId));
        var replacementEntries = replacement.RequireDigestionEntries().ToDictionary(
            static entry => (entry.SourceId, entry.AtomId));
        foreach (var key in currentEntries.Keys.Except(replacementEntries.Keys))
        {
            throw new InvalidOperationException(
                $"ingest cannot remove directory ledger atom {key.AtomId}");
        }

        var atomPaths = ExistingAtomPaths(entries.Keys);
        foreach (var (key, replacementEntry) in replacementEntries)
        {
            if (currentEntries.TryGetValue(key, out var currentEntry))
            {
                var currentBytes = BackfillInventoryWriter.WriteAtom(currentEntry);
                var replacementBytes = BackfillInventoryWriter.WriteAtom(replacementEntry);
                var currentPath = ExistingAtomPath(atomPaths, key.SourceId, key.AtomId);
                var replacementPath = NewAtomPath(replacementEntry);
                if (currentPath == replacementPath
                    && currentBytes.AsSpan().SequenceEqual(replacementBytes.AsSpan()))
                {
                    continue;
                }

                entries.Remove(currentPath);
                if (!entries.TryAdd(
                        replacementPath,
                        new RawRepositoryEntry(replacementPath, replacementBytes)))
                {
                    throw new InvalidOperationException(
                        $"directory ledger atom path already exists: {replacementPath}");
                }

                continue;
            }

            var path = NewAtomPath(replacementEntry);
            if (!entries.TryAdd(
                    path,
                    new RawRepositoryEntry(path, BackfillInventoryWriter.WriteAtom(replacementEntry))))
            {
                throw new InvalidOperationException($"directory ledger atom path already exists: {path}");
            }
        }

        return RawRepositorySnapshot.Create(entries.Values.OrderBy(
            static entry => entry.Path,
            StringComparer.Ordinal));
    }

    private static bool SourceMetadataEquals(
        DigestionLedgerSource current,
        DigestionLedgerSource replacement) =>
        string.Equals(current.SourcePath, replacement.SourcePath, StringComparison.Ordinal)
        && string.Equals(current.Atomizer, replacement.Atomizer, StringComparison.Ordinal)
        && current.GenreRegistryCheck.Kind == replacement.GenreRegistryCheck.Kind
        && current.GenreRegistryCheck.UnregisteredGenres.SequenceEqual(
            replacement.GenreRegistryCheck.UnregisteredGenres,
            StringComparer.Ordinal)
        && current.AcknowledgedStale.SequenceEqual(replacement.AcknowledgedStale);

    // Indexes every ledger path by its source directory and atom file name, so
    // each atom's existing path is one probe instead of a scan of the snapshot.
    private static ILookup<(string SourceId, string AtomId), string> ExistingAtomPaths(
        IEnumerable<string> paths)
    {
        const string extension = ".yaml";
        return paths
            .Where(static path =>
                path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
                && path.EndsWith(extension, StringComparison.Ordinal))
            .Select(static path =>
            {
                var sourceEnd = path.IndexOf('/', BackfillInventoryLoader.RootPath.Length);
                var nameStart = path.LastIndexOf('/') + 1;
                return (Path: path, SourceEnd: sourceEnd, NameStart: nameStart);
            })
            .Where(static item => item.SourceEnd >= 0)
            .ToLookup(
                static item => (
                    item.Path[BackfillInventoryLoader.RootPath.Length..item.SourceEnd],
                    item.Path[item.NameStart..^extension.Length]),
                static item => item.Path);
    }

    private static string ExistingAtomPath(
        ILookup<(string SourceId, string AtomId), string> atomPaths,
        string sourceId,
        string atomId)
    {
        var matches = atomPaths[(sourceId, atomId)].ToArray();
        return matches.Length == 1
            ? matches[0]
            : throw new InvalidOperationException(
                $"directory ledger atom {sourceId}/{atomId} does not have exactly one canonical path");
    }
}
