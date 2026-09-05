using System.Collections.Immutable;

namespace StrataLint.Engine;

/// The report-derived managed import relation used by ledger and admission consumers.
/// It deliberately does not perform cycle detection; Lean validation and the report producer
/// already establish the accepted report boundary.
internal static class LeanImportAdjacency
{
    internal static ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> Build(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);

        var managedPaths = snapshot.Files.Keys
            .Where(static path => LeanClosureValidator.IsManagedLean(path.Value))
            .ToImmutableHashSet();
        var pathsByModule = managedPaths
            .ToImmutableDictionary(LeanImportClosure.ModuleName, StringComparer.Ordinal);
        return managedPaths.ToImmutableDictionary(
            path => path,
            path => lean.Report.Files.TryGetValue(path, out var report)
                ? report.Imports
                    .Distinct(StringComparer.Ordinal)
                    .Select(import => pathsByModule.TryGetValue(import, out var dependency)
                        ? dependency
                        : (RepoPath?)null)
                    .Where(static dependency => dependency is not null)
                    .Select(static dependency => dependency!)
                    .OrderBy(static dependency => dependency.Value, StringComparer.Ordinal)
                    .ToImmutableArray()
                : ImmutableArray<RepoPath>.Empty);
    }

    internal static ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> BuildFromSources(
        RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);

        var managedPaths = snapshot.Files.Keys
            .Where(static path => LeanClosureValidator.IsManagedLean(path.Value))
            .ToImmutableHashSet();
        var pathsByModule = managedPaths
            .ToImmutableDictionary(LeanImportClosure.ModuleName, StringComparer.Ordinal);
        return managedPaths.ToImmutableDictionary(
            path => path,
            path => LeanSourceCatalog.ParseFileImports(snapshot.Files[path])
                .Select(import => pathsByModule.TryGetValue(import, out var dependency)
                    ? dependency
                    : (RepoPath?)null)
                .Where(static dependency => dependency is not null)
                .Select(static dependency => dependency!)
                .OrderBy(static dependency => dependency.Value, StringComparer.Ordinal)
                .ToImmutableArray());
    }

    /// Enumerates the transitive closure of roots in dependency-first order.
    internal static ImmutableArray<RepoPath> DependenciesFirst(
        IEnumerable<RepoPath> roots,
        IReadOnlyDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency)
    {
        ArgumentNullException.ThrowIfNull(roots);
        ArgumentNullException.ThrowIfNull(adjacency);

        var result = ImmutableArray.CreateBuilder<RepoPath>();
        var visited = new HashSet<RepoPath>();
        foreach (var root in roots.OrderBy(static path => path.Value, StringComparer.Ordinal))
        {
            Visit(root);
        }

        return result.ToImmutable();

        void Visit(RepoPath path)
        {
            if (!visited.Add(path))
            {
                return;
            }

            if (adjacency.TryGetValue(path, out var dependencies))
            {
                foreach (var dependency in dependencies)
                {
                    Visit(dependency);
                }
            }

            result.Add(path);
        }
    }
}
