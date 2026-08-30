using Trureturing.Truth;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static bool LeanReportAffected(RuleEvaluationContext context) =>
        Changed(context, IsLeanReportInput);

    private static bool SorryAffected(RuleEvaluationContext context) =>
        LeanReportAffected(context)
        || Changed(context, static path =>
            FrozenLedgerChangeClassifier.IsAcceptedEventPath(path));

    private static bool CapacityAffected(RuleEvaluationContext context) =>
        Changed(context, static path =>
            !IsCapacityExcluded(path)
            || path.EndsWith(".cs", StringComparison.Ordinal)
            || path.EndsWith(".csproj", StringComparison.Ordinal));

    private static bool MirrorsAffected(RuleEvaluationContext context) =>
        Changed(context, static path =>
            IsManagedLeanPath(path)
            || path.StartsWith("Blueprint/", StringComparison.Ordinal)
            || path.StartsWith("Evidence/", StringComparison.Ordinal));

    private static bool ChronicleAffected(RuleEvaluationContext context) =>
        Changed(context, static path => path.StartsWith("Chronicle/", StringComparison.Ordinal));

    private static bool TheoryVolumeAffected(RuleEvaluationContext context) =>
        Changed(context, IsTheoryVolumePath);

    private static bool StatusAffected(RuleEvaluationContext context) =>
        Changed(context, IsStatusScope);

    private static bool HeartsAffected(RuleEvaluationContext context) =>
        Changed(context, static path =>
            path is HeartsPath or HeartsAuthorizationLedger.Path
            || FrozenLedgerChangeClassifier.IsAcceptedEventPath(path));

    private static bool DomainsAffected(RuleEvaluationContext context) =>
        Changed(context, static path =>
            path is "Meta/domains.yaml" or "Meta/registry.yaml"
            || path.StartsWith("D5/", StringComparison.Ordinal)
            || path.StartsWith("Blueprint/D5/", StringComparison.Ordinal)
            || path.StartsWith("Evidence/D5/", StringComparison.Ordinal));

    private static bool FormalSourceAffected(RuleEvaluationContext context) =>
        Changed(context, IsManagedLeanPath);

    private static bool RepositoryShapeAffected(RuleEvaluationContext context) =>
        !context.Changes.Paths.IsEmpty;

    private static bool AnchorsAffected(RuleEvaluationContext context) =>
        Changed(context, static path => path == "Library/queries.yaml")
        || LiteratureReferenceChanged(context);

    private static bool LedgerAffected(RuleEvaluationContext context) =>
        Changed(context, static path =>
            path.EndsWith(".json", StringComparison.Ordinal)
            || path.EndsWith(".yaml", StringComparison.Ordinal)
            || path.EndsWith(".yml", StringComparison.Ordinal)
            || path.StartsWith("Chronicle/", StringComparison.Ordinal)
            || IsManagedLeanPath(path)
            || IsLedgerPolicyDataPath(path)
            || StrataLintEngineBuildInputs.ContainsJudgeSource(path));

    private static bool InstantiationAffected(RuleEvaluationContext context) =>
        Changed(context, static path =>
        {
            var parts = path.Split('/');
            var theory = parts.Length > 1 && parts[0] is "Blueprint" or "Evidence"
                ? parts[1]
                : parts[0];
            return theory is "Metallic" or "Moduli"
                || theory.Length > 1
                    && theory[0] == 'D'
                    && theory != "D5"
                    && theory[1..].All(char.IsDigit);
        });

    private static bool BootstrapAffected(RuleEvaluationContext context) =>
        context.Changes.Paths.Any(BootstrapGate.IsProtected);

    private static bool DescribeLatexAffected(RuleEvaluationContext context) =>
        LeanReportAffected(context)
        || Changed(context, static path =>
            path.StartsWith("Blueprint/", StringComparison.Ordinal)
                && (path.EndsWith(".scribe.cs", StringComparison.Ordinal)
                    || RepositoryPathPolicy.IsBlueprintContentCompositionBuildFile(path))
            || path.StartsWith("tools/", StringComparison.Ordinal));

    private static bool BlueprintSkeletonAffected(RuleEvaluationContext context) =>
        Changed(context, static path =>
            path.StartsWith("Blueprint/", StringComparison.Ordinal)
            && (path.EndsWith(".md", StringComparison.Ordinal)
                || path.EndsWith(".scribe.cs", StringComparison.Ordinal)));

    private static bool ScribeSourceAffected(RuleEvaluationContext context) =>
        Changed(context, static path =>
            path.StartsWith("Blueprint/", StringComparison.Ordinal)
            && path.EndsWith(".scribe.cs", StringComparison.Ordinal));

    private static bool Changed(
        RuleEvaluationContext context,
        Func<string, bool> predicate) =>
        context.Changes.Paths.Any(path => predicate(path.Value));

    private static bool IsManagedLeanPath(string path) =>
        path == "Trureturing.lean"
        || path.StartsWith("D5/", StringComparison.Ordinal)
            && path.EndsWith(".lean", StringComparison.Ordinal);

    private static bool IsLeanReportInput(string path) =>
        FrozenLedgerDeltaPredicate.IsManagedLeanSource(path)
        || FrozenLedgerDeltaPredicate.IsEnvironmentInput(path)
        || FrozenLedgerDeltaPredicate.IsDeltaDefinitionInput(path);

    internal static bool IsLeanClosureFactAffected(
        RuleEvaluationContext context,
        RepoPath source) =>
        LeanImportClosure.RepositoryPaths(context.Lean.Report, source)
            .Any(path => context.IsBaseFactAffected(path.Value))
        || context.Changes.Paths.Any(path =>
            IsLeanReportInput(path.Value) && !IsManagedLeanPath(path.Value));

    private static bool LiteratureReferenceChanged(RuleEvaluationContext context)
    {
        if (!context.Current.TryGetFile("Library/queries.yaml", out var file))
        {
            return false;
        }

        try
        {
            if (YamlSubsetParser.Parse(file.Text) is not Dictionary<string, object?> root
                || !root.TryGetValue("queries", out var rawQueries)
                || rawQueries is not List<object?> queries)
            {
                return false;
            }

            var references = new HashSet<string>(StringComparer.Ordinal);
            foreach (var query in queries.OfType<Dictionary<string, object?>>())
            {
                if (query.GetValueOrDefault("source_path") is string sourcePath)
                {
                    references.Add(sourcePath);
                }

                if (query.GetValueOrDefault("target_gid") is string target
                    && Gid.TryParse(target, out var gid))
                {
                    references.Add(gid.Path.Value);
                }
            }

            return context.Changes.Paths.Any(path => references.Contains(path.Value));
        }
        catch (FormatException)
        {
            return false;
        }
    }
}
