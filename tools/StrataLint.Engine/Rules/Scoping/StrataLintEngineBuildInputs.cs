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
    private const string RepositoryPathPolicyPath =
        ProjectDirectory + "/Coordinates/RepositoryPathPolicy.cs";
    private const string RepositoryPathPolicyPathsPath =
        ProjectDirectory + "/Coordinates/RepositoryPathPolicy.Paths.cs";
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
        if (ContainsRuleSource(path))
        {
            return true;
        }

        if (path == HeartsAuthorizationLedgerPath
            || path == FrozenAcceptedEventLoaderPath
            || path == TrustedRevocationReceiptsPath
            || path == RepositoryPathPolicyPath
            || path == RepositoryPathPolicyPathsPath)
        {
            return true;
        }

        return IsInheritedBuildInput(path);
    }

    internal static bool ContainsRuleSource(string path) =>
        path == ProjectPath
        || path.StartsWith(RulesDirectory + "/", StringComparison.Ordinal)
            && path.EndsWith(".cs", StringComparison.Ordinal);

    /// <summary>
    /// The judge-source side of the CI judge content address. Every non-test path under
    /// <c>tools/</c> can change the program that interprets repository facts. Blueprint scribe
    /// definitions are also judge source because <c>tools/StrataLint.Scribe/StrataLint.Scribe.csproj</c>
    /// compiles <c>Blueprint/**/*.scribe.cs</c>. Membership is therefore structural rather than a
    /// list of today's transitive helpers.
    /// </summary>
    internal static bool ContainsJudgeSource(string path) =>
        path.StartsWith("tools/", StringComparison.Ordinal)
            && !path.StartsWith("tools/tests/", StringComparison.Ordinal)
        || path.StartsWith("Blueprint/", StringComparison.Ordinal)
            && path.EndsWith(".scribe.cs", StringComparison.Ordinal);

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
