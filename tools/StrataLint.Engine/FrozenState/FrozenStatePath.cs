using System.Diagnostics.CodeAnalysis;

namespace StrataLint.Engine;

internal static class FrozenStatePath
{
    internal const string Root = "Golden/Frozen/state/";

    internal static bool IsUnderRoot(string? path) =>
        path is not null && path.StartsWith(Root, StringComparison.Ordinal);

    internal static bool TryToModulePath(
        string? statePath,
        [NotNullWhen(true)] out RepoPath? modulePath)
    {
        modulePath = null;
        const string suffix = ".json";
        if (statePath is null
            || !IsUnderRoot(statePath)
            || !statePath.EndsWith(".lean.json", StringComparison.Ordinal))
        {
            return false;
        }

        var candidate = statePath[Root.Length..^suffix.Length];
        if (!RepoPath.TryCreate(candidate, out var path)
            || !RepositoryPathPolicy.TryResolve(path, out var gid)
            || gid?.ToTarget() is not Target.Formal
            || gid.Path != path)
        {
            return false;
        }

        modulePath = path;
        return true;
    }

    internal static RepoPath FromModulePath(RepoPath modulePath)
    {
        ArgumentNullException.ThrowIfNull(modulePath);
        if (!RepositoryPathPolicy.TryResolve(modulePath, out var gid)
            || gid?.ToTarget() is not Target.Formal
            || gid.Path != modulePath)
        {
            throw new ArgumentException(
                $"Module path is not a canonical D5 Lean selector: {modulePath.Value}.",
                nameof(modulePath));
        }

        var statePath = RepoPath.CreateKnown(Root + modulePath.Value + ".json");
        if (!TryToModulePath(statePath.Value, out var inverse) || inverse != modulePath)
        {
            throw new InvalidOperationException("Frozen state path does not have an exact module inverse.");
        }

        return statePath;
    }
}
