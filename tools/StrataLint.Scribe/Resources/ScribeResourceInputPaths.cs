namespace StrataLint.Scribe;

internal static class ScribeResourceInputPaths
{
    internal const string BlueprintDirectoryName = "Blueprint";
    internal const string ProjectionDirectoryName = "Golden/Projection";

    internal static string BlueprintDirectory(string repositoryRoot) =>
        Path.Combine(repositoryRoot, BlueprintDirectoryName);

    internal static string ProjectionDirectory(string repositoryRoot) =>
        Path.Combine(repositoryRoot, ProjectionDirectoryName.Replace('/', Path.DirectorySeparatorChar));
}
