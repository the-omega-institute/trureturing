using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private const string BlueprintPrefix = "Blueprint/";

    private static ImmutableArray<RuleFinding> ScribeLegacyConstructorBudget(RuleEvaluationContext context)
    {
        var paths = context.Changes.Paths
            .Where(static path => IsBlueprintPath(path.Value, ".scribe.cs"))
            .ToImmutableArray();
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();

        foreach (var path in paths.Where(path => context.Current.Files.ContainsKey(path)))
        {
            var current = ScribeLegacyConstructorScanner.Count(context.Current.Files[path].Text);
            foreach (var kind in Enum.GetValues<ScribeLegacyConstructor>())
            {
                if (current[kind] > 0)
                {
                    findings.Add(new RuleFinding(
                        path.Value,
                        $"legacy Scribe constructor {kind} is present {current[kind]} time(s); the Scribe migration retired it; use the report-derived interface"));
                }
            }
        }
        return findings.ToImmutable();
    }

    private static bool IsBlueprintPath(string path, string suffix) =>
        path.StartsWith(BlueprintPrefix, StringComparison.Ordinal)
        && path.EndsWith(suffix, StringComparison.Ordinal);
}
