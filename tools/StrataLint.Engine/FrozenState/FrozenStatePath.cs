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
            || !IsCanonicalModulePath(path))
        {
            return false;
        }

        modulePath = path;
        return true;
    }

    internal static RepoPath FromModulePath(RepoPath modulePath)
    {
        ArgumentNullException.ThrowIfNull(modulePath);
        if (!TryFromModulePath(modulePath, out var statePath))
        {
            throw new ArgumentException(
                $"Module path is not a canonical repository Lean module: {modulePath.Value}.",
                nameof(modulePath));
        }

        return statePath;
    }

    internal static bool TryFromModulePath(
        RepoPath? modulePath,
        [NotNullWhen(true)] out RepoPath? statePath)
    {
        statePath = null;
        if (modulePath is null || !IsCanonicalModulePath(modulePath))
        {
            return false;
        }

        var candidate = RepoPath.CreateKnown(Root + modulePath.Value + ".json");
        if (!TryToModulePath(candidate.Value, out var inverse) || inverse != modulePath)
        {
            return false;
        }

        statePath = candidate;
        return true;
    }

    internal static bool IsCanonicalModulePath(RepoPath path)
    {
        ArgumentNullException.ThrowIfNull(path);
        const string suffix = ".lean";
        if (!path.Value.EndsWith(suffix, StringComparison.Ordinal))
        {
            return false;
        }

        var moduleName = path.Value[..^suffix.Length];
        return moduleName.Split('/').All(IsCanonicalModuleSegment);
    }

    private static bool IsCanonicalModuleSegment(string segment) =>
        segment.Length > 0
        && segment[0] is >= 'A' and <= 'Z'
        && segment.Skip(1).All(static character =>
            character is >= 'A' and <= 'Z'
                or >= 'a' and <= 'z'
                or >= '0' and <= '9'
                or '_');
}
