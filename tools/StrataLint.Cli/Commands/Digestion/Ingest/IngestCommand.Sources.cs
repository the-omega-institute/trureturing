using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    private static InvalidOperationException SourceUsage(string reason) => new(
        "USAGE: StrataLint ingest --source X [--source X ...]; " + reason);

    private static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) ReadSelectedSources(
        IRepositoryGateway repository, ImmutableArray<string> selectors)
    {
        var paths = new HashSet<string>(StringComparer.Ordinal) { TheoryAtomizerDataLoader.DataPath };
        RawRepositorySnapshot? metadata = null;
        foreach (var selector in selectors)
        {
            if (!RepoPath.TryCreate(selector, out _)) throw SourceUsage($"unknown --source selector '{selector}'");
            if (!selector.Contains('/'))
            {
                paths.Add(BackfillInventoryLoader.RootPath + selector + "/source.toml");
                continue;
            }
            metadata ??= DigestionQuerySelection.FindSourceMetadata(repository,
                selectors.Where(static source => source.Contains('/')).ToArray());
            var matches = metadata.Entries.Where(entry => DigestionQuerySelection.MatchesSourcePath(entry, selector)).ToArray();
            if (matches.Length > 1) throw SourceUsage($"ambiguous --source selector '{selector}'");
            if (matches.Length == 1) paths.Add(matches[0].Path);
            else paths.Add(BackfillInventoryLoader.RootPath + DigestionIngestor.DeriveSourceId(selector) + "/source.toml");
            paths.Add(selector);
        }
        var loaded = DigestionQuerySelection.Load(repository.ReadCurrent(paths.Select(DigestionQuerySelection.Literal).ToArray()));
        if (loaded.Document.RequireDigestionSources().IsEmpty) return loaded;
        return DigestionQuerySelection.Load(DigestionQuerySelection.Merge(loaded.Raw,
            repository.ReadCurrent(loaded.Document.RequireDigestionSources()
                .Select(static source => DigestionQuerySelection.Literal(source.SourcePath)).ToArray())));
    }

    private static (ImmutableHashSet<string>? SourceIds, ImmutableHashSet<string>? RegistrationPaths) ResolveSources(
        BackfillInventoryDocument document,
        RepositorySnapshot current,
        ImmutableArray<string> selectors)
    {
        if (selectors.IsEmpty) return (null, null);

        var sources = document.RequireDigestionSources();
        var claims = sources.ToDictionary(static source => source.SourceId,
            static source => source.SourcePath, StringComparer.Ordinal);
        var ids = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var paths = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        foreach (var selector in selectors)
        {
            var registered = sources.FirstOrDefault(source => source.SourceId == selector || source.SourcePath == selector);
            if (registered is not null)
            {
                ids.Add(registered.SourceId);
                continue;
            }
            if (!selector.StartsWith(DigestionOpaquePathPolicy.TheoryRootPath, StringComparison.Ordinal)
                || !selector.EndsWith(".md", StringComparison.Ordinal)
                || !current.TryGetFile(selector, out _))
                throw SourceUsage($"unknown --source selector '{selector}'");

            var id = DigestionIngestor.DeriveSourceId(selector);
            if (claims.TryGetValue(id, out var claimant) && claimant != selector)
                throw SourceUsage($"--source selector '{selector}' collides with '{claimant}': {id}");
            claims[id] = selector;
            ids.Add(id);
            paths.Add(selector);
        }
        return (ids.ToImmutable(), paths.ToImmutable());
    }

}
