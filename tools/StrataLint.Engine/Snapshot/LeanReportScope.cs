using System.Collections.Immutable;

namespace StrataLint.Engine;

/// <summary>
/// An independently selected set of Lean module paths and its source-derived
/// repository import closure.  Report consumers must construct this value from
/// their explicit request targets; a report cannot enlarge its own scope.
/// </summary>
internal sealed class LeanReportScope
{
    private LeanReportScope(RepositorySnapshot sourceSnapshot, ImmutableHashSet<RepoPath> paths)
    {
        SourceSnapshot = sourceSnapshot;
        Paths = paths;
    }

    internal RepositorySnapshot SourceSnapshot { get; }

    internal ImmutableHashSet<RepoPath> Paths { get; }

    internal static LeanReportScope Create(
        RepositorySnapshot sourceSnapshot,
        IEnumerable<RepoPath> requestedTargets)
    {
        ArgumentNullException.ThrowIfNull(sourceSnapshot);
        ArgumentNullException.ThrowIfNull(requestedTargets);

        var roots = requestedTargets
            .Distinct()
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        if (roots.IsEmpty)
            throw new ArgumentException("scoped Lean report targets must be nonempty", nameof(requestedTargets));

        var modules = sourceSnapshot.Files
            .Where(static item => LeanClosureValidator.IsReportLean(item.Key.Value))
            .ToDictionary(
                static item => ModuleName(item.Key),
                static item => (Path: item.Key, File: item.Value),
                StringComparer.Ordinal);
        var pending = new Stack<RepoPath>();
        foreach (var root in roots)
        {
            if (!LeanClosureValidator.IsReportLean(root.Value)
                || !sourceSnapshot.Files.ContainsKey(root))
            {
                throw new InvalidOperationException(
                    $"scoped Lean report target does not exist or is not a report module: {root.Value}");
            }

            pending.Push(root);
        }

        var paths = ImmutableHashSet.CreateBuilder<RepoPath>();
        while (pending.TryPop(out var path))
        {
            if (!paths.Add(path)) continue;
            var imports = LeanSourceCatalog.ParseFileImports(sourceSnapshot.Files[path]);
            foreach (var import in imports)
            {
                if (modules.TryGetValue(import, out var dependency))
                {
                    pending.Push(dependency.Path);
                    continue;
                }

                // Repository-owned Lean modules have a path in the source
                // snapshot.  A missing one is a broken authoritative closure;
                // package/toolchain imports are intentionally external.
                if (IsRepositoryModule(import))
                {
                    throw new InvalidOperationException(
                        $"scoped Lean report import closure is missing module {import} imported by {path.Value}");
                }
            }
        }

        return new LeanReportScope(sourceSnapshot, paths.ToImmutable());
    }

    private static bool IsRepositoryModule(string module) =>
        module == "Trureturing"
        || module.StartsWith("D5.", StringComparison.Ordinal)
        || module.StartsWith("Reg.", StringComparison.Ordinal);

    private static string ModuleName(RepoPath path) => path.Value == "Trureturing.lean"
        ? "Trureturing"
        : path.Value[..^5].Replace('/', '.');
}
