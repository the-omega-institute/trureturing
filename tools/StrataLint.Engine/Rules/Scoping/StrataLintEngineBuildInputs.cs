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
    internal static bool Contains(string path, IReadOnlySet<string> registeredInputs)
    {
        if (path == ProjectPath
            || path.StartsWith(ProjectDirectory + "/", StringComparison.Ordinal)
                && path.EndsWith(".cs", StringComparison.Ordinal))
        {
            return true;
        }

        return registeredInputs.Contains(path);
    }

    internal static bool ContainsRuleImplementation(string path, IReadOnlySet<string> registeredInputs)
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

        return registeredInputs.Contains(path);
    }

    internal static bool ContainsRuleSource(string path) =>
        path == ProjectPath
        || path.StartsWith(RulesDirectory + "/", StringComparison.Ordinal)
            && path.EndsWith(".cs", StringComparison.Ordinal);

    /// <summary>Non-test tool sources belong to the judge build inputs.</summary>
    internal static bool ContainsJudgeSource(string path) =>
        path.StartsWith("tools/", StringComparison.Ordinal)
            && !path.StartsWith("tools/tests/", StringComparison.Ordinal);

}
