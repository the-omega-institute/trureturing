using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class MathlibUpgradePropositionSourceDiagnostics
{
    internal static ImmutableArray<RepoPath> FindFailures(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        ImmutableHashSet<RepoPath> reanchoredPaths,
        FrozenStateCatalog baseState,
        LeanAxiomReport candidateReport)
    {
        var failures = ImmutableArray.CreateBuilder<RepoPath>();
        var baseSources = LeanSourceCatalog.Parse(protectedBase);
        var candidateSources = LeanSourceCatalog.Parse(candidate);
        var originalClosures = SourceClosures(protectedBase);
        var candidateClosures = SourceClosures(candidate);
        foreach (var path in reanchoredPaths.OrderBy(
            static path => path.Value,
            StringComparer.Ordinal))
        {
            try
            {
                if (!baseState.Records.TryGetValue(path, out var recorded)
                    || !candidateReport.Files.TryGetValue(path, out var current)
                    || !SourceBytesMatch(originalClosures(path), candidateClosures(path))
                        && !baseSources.ExtractPropositionSource(
                                path,
                                recorded.Declarations)
                            .AsSpan().SequenceEqual(candidateSources.ExtractPropositionSource(
                                path,
                                FrozenStateRecord.Project(current)).AsSpan()))
                {
                    failures.Add(path);
                }
            }
            catch (LeanSourceExtractionException)
            {
                failures.Add(path);
            }
        }

        return failures.ToImmutable();
    }

    private static bool SourceBytesMatch(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate) =>
        protectedBase.Files.Count == candidate.Files.Count
        && protectedBase.Files.All(item => candidate.Files.TryGetValue(item.Key, out var file)
            && item.Value.RawBytes.AsSpan().SequenceEqual(file.RawBytes.AsSpan()));

    private static Func<RepoPath, RepositorySnapshot> SourceClosures(RepositorySnapshot snapshot)
    {
        var sources = snapshot.Files.Values.Where(file => LeanClosureValidator.IsManagedLean(file.Path.Value))
            .ToDictionary(file => LeanImportClosure.ModuleName(file.Path), StringComparer.Ordinal);
        var imports = new Dictionary<RepoPath, ImmutableArray<string>>();
        return path =>
        {
            var selected = new Dictionary<RepoPath, RepositoryFile>();
            var pending = new Queue<RepoPath>();
            pending.Enqueue(path);
            while (pending.TryDequeue(out var next))
            {
                if (selected.ContainsKey(next)) continue;
                if (!snapshot.Files.TryGetValue(next, out var file))
                    throw new LeanSourceExtractionException($"missing retained proposition source {next.Value}");
                selected.Add(next, file);
                if (!imports.TryGetValue(next, out var dependencies))
                {
                    dependencies = LeanSourceCatalog.ParseFileImports(file);
                    imports.Add(next, dependencies);
                }
                foreach (var dependency in dependencies)
                    if (sources.TryGetValue(dependency, out var source)) pending.Enqueue(source.Path);
            }
            return RepositorySnapshot.Create(selected.ToImmutableDictionary());
        };
    }
}
