namespace StrataLint.Engine;

internal static class StrataLintEngineBuildInputs
{
    private const string ProjectDirectory = "tools/StrataLint.Engine";
    private const string ProjectPath = ProjectDirectory + "/StrataLint.Engine.csproj";
    private const string RulesDirectory = ProjectDirectory + "/Rules";
    private const string HeartsAuthorizationLedgerPath =
        ProjectDirectory + "/Authorization/HeartsAuthorizationLedger.cs";
    private const string FrozenAcceptedEventLoaderPath =
        ProjectDirectory + "/Ledger/FrozenAcceptedEventLoader.cs";
    private const string TrustedRevocationReceiptsPath =
        ProjectDirectory + "/Revocation/TrustedRevocationReceipts.cs";

    internal static bool Contains(string path)
    {
        if (path == ProjectPath
            || path.StartsWith(ProjectDirectory + "/", StringComparison.Ordinal)
                && path.EndsWith(".cs", StringComparison.Ordinal))
        {
            return true;
        }

        return IsInheritedBuildInput(path);
    }

    internal static bool ContainsRuleImplementation(string path)
    {
        if (path == ProjectPath
            || path.StartsWith(RulesDirectory + "/", StringComparison.Ordinal)
                && path.EndsWith(".cs", StringComparison.Ordinal))
        {
            return true;
        }

        if (path == HeartsAuthorizationLedgerPath
            || path == FrozenAcceptedEventLoaderPath
            || path == TrustedRevocationReceiptsPath)
        {
            return true;
        }

        return IsInheritedBuildInput(path);
    }

    private static bool IsInheritedBuildInput(string path)
    {
        var separator = path.LastIndexOf('/');
        var directory = separator < 0 ? string.Empty : path[..separator];
        if (!IsAncestor(directory, ProjectDirectory))
        {
            return false;
        }

        var fileName = path[(separator + 1)..];
        return fileName == "global.json"
            || fileName.StartsWith("Directory.Build.", StringComparison.Ordinal)
            || fileName.StartsWith("Directory.Packages.", StringComparison.Ordinal)
            || fileName.Equals("NuGet.Config", StringComparison.OrdinalIgnoreCase)
            || fileName == "packages.lock.json";
    }

    private static bool IsAncestor(string directory, string descendant) =>
        directory.Length == 0
        || descendant == directory
        || descendant.StartsWith(directory + "/", StringComparison.Ordinal);
}
