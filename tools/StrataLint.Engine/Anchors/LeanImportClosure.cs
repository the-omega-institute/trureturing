using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class LeanImportClosure
{
    internal static bool RepositoryClosureIsUnchanged(
        AcyclicTruthDag dag,
        RepoPath startPath,
        RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(dag);
        ArgumentNullException.ThrowIfNull(changes);
        return !RepositoryPaths(dag, startPath).Overlaps(changes.Paths);
    }

    internal static ImmutableHashSet<RepoPath> RepositoryPaths(
        AcyclicTruthDag dag,
        RepoPath startPath)
    {
        ArgumentNullException.ThrowIfNull(dag);
        var paths = ImmutableHashSet.CreateBuilder<RepoPath>();
        var pending = new Stack<RepoPath>();
        pending.Push(startPath);
        while (pending.TryPop(out var path))
        {
            if (!paths.Add(path))
            {
                continue;
            }

            foreach (var dependency in dag.DependenciesOf(path))
            {
                pending.Push(dependency);
            }
        }

        return paths.ToImmutable();
    }

    internal static ImmutableHashSet<RepoPath> RepositoryPaths(
        LeanAxiomReport report,
        RepoPath startPath)
    {
        ArgumentNullException.ThrowIfNull(report);
        var pathsByModule = report.Files.Keys.ToDictionary(
            ModuleName,
            static path => path,
            StringComparer.Ordinal);
        var paths = ImmutableHashSet.CreateBuilder<RepoPath>();
        var pending = new Stack<RepoPath>();
        pending.Push(startPath);
        while (pending.TryPop(out var path))
        {
            if (!paths.Add(path) || !report.Files.TryGetValue(path, out var file))
            {
                continue;
            }

            foreach (var import in file.Imports)
            {
                if (pathsByModule.TryGetValue(import, out var dependency))
                {
                    pending.Push(dependency);
                }
            }
        }

        return paths.ToImmutable();
    }

    internal static bool ImportsExternalModule(
        LeanAxiomReport report,
        string startModule,
        string targetModule)
    {
        ArgumentNullException.ThrowIfNull(report);
        ArgumentException.ThrowIfNullOrWhiteSpace(startModule);
        ArgumentException.ThrowIfNullOrWhiteSpace(targetModule);

        var reportsByModule = report.Files.ToDictionary(
            static item => ModuleName(item.Key),
            static item => item.Value,
            StringComparer.Ordinal);
        if (!reportsByModule.ContainsKey(startModule))
        {
            return false;
        }

        var pending = new Stack<string>();
        var visited = new HashSet<string>(StringComparer.Ordinal);
        pending.Push(startModule);
        while (pending.TryPop(out var module))
        {
            if (!visited.Add(module) || !reportsByModule.TryGetValue(module, out var file))
            {
                continue;
            }

            foreach (var import in file.Imports)
            {
                if (string.Equals(import, targetModule, StringComparison.Ordinal))
                {
                    return true;
                }

                if (reportsByModule.ContainsKey(import) && !visited.Contains(import))
                {
                    pending.Push(import);
                }
            }
        }

        return false;
    }

    internal static string ModuleName(RepoPath path)
    {
        var value = path.Value;
        return value.EndsWith(".lean", StringComparison.Ordinal)
            ? value[..^5].Replace('/', '.')
            : value.Replace('/', '.');
    }
}
