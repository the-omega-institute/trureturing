using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    // Rewrites one registered source's genre projection from its current bytes.
    // Nothing else in the ledger is touched.
    private static CommandResult RefreshSourceRegistry(
        string root, IRepositoryGateway repository, IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count is not (2 or 3) || arguments[0] != "--refresh-source"
                || string.IsNullOrWhiteSpace(arguments[1])
                || arguments.Count == 3 && arguments[2] != "--plan")
                throw new InvalidOperationException(
                    "USAGE: StrataLint align-digestion-status --refresh-source EXISTING_ID_OR_PATH [--plan]");

            var planOnly = arguments.Count == 3;
            var (currentRaw, current, document) = DigestionWorkingTree.Read(
                repository,
                Decode,
                static snapshot => LoadDocument(snapshot));
            var sources = document.RequireDigestionSources();
            var matches = sources.Where(source => source.SourceId == arguments[1]
                || source.SourcePath == arguments[1]).ToArray();
            if (matches.Length != 1)
                throw new InvalidOperationException("selector must resolve exactly one existing source");
            var selected = matches[0];
            if (!current.TryGetFile(selected.SourcePath, out var sourceFile))
                throw new InvalidOperationException($"source path is dangling: {selected.SourcePath}");
            var atomized = AtomizerRegistry.Atomize(selected.Atomizer, sourceFile.RawBytes.AsSpan(),
                TheoryAtomizerDataLoader.Load(current));
            if (DigestionLedgerAligner.AtomizerIntegrityFailure(atomized, sourceFile.RawBytes.AsSpan()) is { } failure)
                throw new InvalidOperationException($"source {selected.SourceId} atomizer integrity failed: {failure}");
            var replacement = document.WithDigestionSources(sources.Select(source =>
                source.SourceId == selected.SourceId
                    ? source with { GenreRegistryProjection = GenreRegistryProjection.Available(atomized.GenreRegistryCheck) }
                    : source).ToImmutableArray());
            var updates = LedgerUpdates(
                currentRaw, ReplaceLedger(currentRaw, document, replacement), document, replacement);
            var metadataPath = $"{BackfillInventoryLoader.RootPath}{selected.SourceId}/source.toml";
            if (updates.Any(update => update.Path != metadataPath || update.Bytes is null))
                throw new InvalidOperationException("registry refresh would write outside the selected source metadata");
            if (!planOnly)
                ApplyLedgerUpdatesAtomically(root, currentRaw, updates);
            return new CommandResult(
                true,
                $"REGISTRY_REFRESH source={selected.SourceId} path={metadataPath} "
                + $"changed={(updates.Length > 0).ToString().ToLowerInvariant()} "
                + $"applied={(!planOnly).ToString().ToLowerInvariant()}\n",
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"REGISTRY_REFRESH_INVALID {exception.Message}\n");
        }
    }
}
