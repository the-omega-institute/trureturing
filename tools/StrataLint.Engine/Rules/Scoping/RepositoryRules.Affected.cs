using Trureturing.Truth;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static bool RegistrationImportsAffected(DeltaRuleContext context) =>
        Changed(context, static path => path.StartsWith("D5/", StringComparison.Ordinal)
            && path.EndsWith(".lean", StringComparison.Ordinal))
        || Changed(context, path => IsLeanReportProducerInput(path, context.RegisteredRuleBuildInputs));

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

    private static bool LiteratureAffected(DeltaRuleContext context) =>
        Changed(context, static path => path == "Library/queries.yaml")
        || LiteratureReferenceChanged(context);

    private static bool AnchorsAffected(DeltaRuleContext context) =>
        LiteratureAffected(context)
        || Changed(context, static path => path == "Trureturing.lean"
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
        path == "lean-report-inputs.json"
        || path.StartsWith("tools/", StringComparison.Ordinal)
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
    private static bool LiteratureReferenceChanged(DeltaRuleContext context)
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
