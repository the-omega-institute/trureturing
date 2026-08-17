using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static class LeanImportClosure
{
    private static readonly ImmutableHashSet<string> ToolchainModuleRoots =
        ImmutableHashSet.Create(StringComparer.Ordinal, "Init", "Lake", "Lean", "Std");
    private static readonly ImmutableDictionary<string, string> PinnedPackageByModuleRoot =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Batteries"] = "batteries",
            ["Mathlib"] = "mathlib",
        }.ToImmutableDictionary(StringComparer.Ordinal);

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

    internal static bool ExternalImportsHaveNamedPinCoverage(
        LeanAxiomReport report,
        RepoPath startPath,
        RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(report);
        ArgumentNullException.ThrowIfNull(snapshot);
        var external = ExternalImports(report, startPath);
        if (external.IsEmpty)
        {
            return true;
        }

        var packages = PinnedGitPackages(snapshot);
        return external.All(import =>
        {
            var separator = import.IndexOf('.');
            var root = separator < 0 ? import : import[..separator];
            return ToolchainModuleRoots.Contains(root)
                || PinnedPackageByModuleRoot.TryGetValue(root, out var package)
                    && packages.Contains(package);
        });
    }

    private static ImmutableHashSet<string> ExternalImports(
        LeanAxiomReport report,
        RepoPath startPath)
    {
        var reportsByModule = report.Files.ToDictionary(
            static item => ModuleName(item.Key),
            static item => item.Value,
            StringComparer.Ordinal);
        var startModule = ModuleName(startPath);
        if (!reportsByModule.ContainsKey(startModule))
        {
            return ImmutableHashSet<string>.Empty;
        }

        var external = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
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
                if (reportsByModule.ContainsKey(import))
                {
                    pending.Push(import);
                }
                else
                {
                    external.Add(import);
                }
            }
        }

        return external.ToImmutable();
    }

    private static ImmutableHashSet<string> PinnedGitPackages(RepositorySnapshot snapshot)
    {
        var packages = ImmutableHashSet.CreateBuilder<string>(StringComparer.OrdinalIgnoreCase);
        if (!snapshot.TryGetFile("lake-manifest.json", out var manifest))
        {
            return packages.ToImmutable();
        }

        try
        {
            using var document = JsonDocument.Parse(manifest.RawBytes.AsSpan().ToArray());
            if (!document.RootElement.TryGetProperty("packages", out var entries)
                || entries.ValueKind != JsonValueKind.Array)
            {
                return packages.ToImmutable();
            }

            foreach (var entry in entries.EnumerateArray())
            {
                if (entry.ValueKind != JsonValueKind.Object
                    || !entry.TryGetProperty("name", out var name)
                    || name.ValueKind != JsonValueKind.String
                    || string.IsNullOrWhiteSpace(name.GetString())
                    || !entry.TryGetProperty("type", out var type)
                    || type.ValueKind != JsonValueKind.String
                    || type.GetString() != "git"
                    || !entry.TryGetProperty("rev", out var revision)
                    || revision.ValueKind != JsonValueKind.String
                    || string.IsNullOrWhiteSpace(revision.GetString()))
                {
                    continue;
                }

                packages.Add(name.GetString()!);
            }
        }
        catch (JsonException)
        {
            return ImmutableHashSet<string>.Empty.WithComparer(StringComparer.OrdinalIgnoreCase);
        }

        return packages.ToImmutable();
    }

    internal static string ModuleName(RepoPath path)
    {
        var value = path.Value;
        return value.EndsWith(".lean", StringComparison.Ordinal)
            ? value[..^5].Replace('/', '.')
            : value.Replace('/', '.');
    }
}
