using Trureturing.Truth;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static bool CapacityAffected(DeltaRuleContext context) =>
        Changed(context, static path => !IsCapacityExcluded(path));

    private static bool HeartsAffected(DeltaRuleContext context) =>
        Changed(context, static path =>
            path is HeartsPath or HeartsAuthorizationLedger.Path
            || FrozenLedgerChangeClassifier.IsAcceptedEventPath(path)
            || FrozenStatePath.IsUnderRoot(path)
            || path.StartsWith("D5/", StringComparison.Ordinal)
                && path.EndsWith(".lean", StringComparison.Ordinal))
        || Changed(context, path => IsLeanReportProducerInput(path, context.RegisteredRuleBuildInputs));

    private static bool BootstrapAffected(DeltaRuleContext context) =>
        context.Changes.Paths.Any(BootstrapGate.IsProtected);

    private static bool BlueprintSkeletonAffected(DeltaRuleContext context) =>
        Changed(context, static path =>
            path.StartsWith("Blueprint/", StringComparison.Ordinal)
            && (path.EndsWith(".md", StringComparison.Ordinal)
                || path.EndsWith(".scribe.cs", StringComparison.Ordinal)));

    private static bool ScribeSourceAffected(DeltaRuleContext context) =>
        Changed(context, static path =>
            path.StartsWith("Blueprint/", StringComparison.Ordinal)
            && path.EndsWith(".scribe.cs", StringComparison.Ordinal));

    private static bool Changed(
        DeltaRuleContext context,
        Func<string, bool> predicate) =>
        context.Changes.Paths.Any(path => predicate(path.Value));

    internal static bool IsLeanReportProducerInput(string path, IReadOnlySet<string> registeredInputs) =>
        path.StartsWith("tools/", StringComparison.Ordinal)
            && !path.StartsWith("tools/tests/", StringComparison.Ordinal)
        || StrataLintEngineBuildInputs.Contains(path, registeredInputs)
        || path.StartsWith(".github/workflows/", StringComparison.Ordinal)
        || FrozenLedgerDeltaPredicate.IsEnvironmentInput(path);

    internal static bool IsLeanClosureFactAffected(
        DeltaRuleContext context,
        RepoPath source) =>
        LeanImportClosure.RepositoryPaths(context.Lean.Report, source)
            .Any(path => context.IsBaseFactAffected(path.Value))
        || Changed(context, path => IsLeanReportProducerInput(path, context.RegisteredRuleBuildInputs));


}
