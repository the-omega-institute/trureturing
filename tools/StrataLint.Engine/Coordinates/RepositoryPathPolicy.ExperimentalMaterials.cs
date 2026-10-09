namespace StrataLint.Engine;

internal static partial class RepositoryPathPolicy
{
    internal const string ExperimentalMaterialsMessage =
        "experimental programs, data and reports belong in the separate "
        + "trureturing-experiments repository; only the reports entrypoint, "
        + "licenses and notices may remain here";

    internal static bool IsExperimentalMaterialPath(string path)
    {
        if (path.StartsWith("experiments/", StringComparison.Ordinal)
            || path.StartsWith("Evidence/D5/experiments/", StringComparison.Ordinal))
            return true;
        if (!path.StartsWith(ReportsRootPath, StringComparison.Ordinal)
            || path == ReportsRootPath + "README.md")
            return false;

        if (path.StartsWith(ReportsRootPath + "licenses/", StringComparison.Ordinal)
            && path.EndsWith(".md", StringComparison.Ordinal))
            return false;

        var name = path[(path.LastIndexOf('/') + 1)..];
        return !name.EndsWith(".txt", StringComparison.Ordinal)
            || !(name.Contains("LICENSE", StringComparison.OrdinalIgnoreCase)
                || name.Contains("NOTICE", StringComparison.OrdinalIgnoreCase));
    }
}
